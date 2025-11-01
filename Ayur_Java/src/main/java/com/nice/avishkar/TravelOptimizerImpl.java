package com.nice.avishkar;


import java.io.IOException;
import java.net.URL;
import java.net.HttpURLConnection;
import java.io.InputStreamReader;
import java.io.BufferedReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.nio.charset.StandardCharsets;
import java.util.Map;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Comparator;



public class TravelOptimizerImpl implements ITravelOptimizer {

    private final boolean generateSummary;

    TravelOptimizerImpl(boolean generateSummary)
    {
        this.generateSummary = generateSummary;
    }

    public Map<String, OptimalTravelSchedule> getOptimalTravelOptions(ResourceInfo resourceInfo) throws IOException {
        List<ScheduleRecord> schedules = readSchedules(resourceInfo.getTransportSchedulePath());
        List<CustomerRequest> requests = readRequests(resourceInfo.getCustomerRequestPath());

        Map<Integer, ScheduleRecord> idxToSchedule = new HashMap<>();
        for (int i = 0; i < schedules.size(); i++) idxToSchedule.put(i, schedules.get(i));

        Map<String, List<Integer>> departuresFrom = new HashMap<>();
        for (int i = 0; i < schedules.size(); i++) {
            departuresFrom.computeIfAbsent(schedules.get(i).source, k -> new ArrayList<>()).add(i);
        }

        java.util.concurrent.ConcurrentMap<String, OptimalTravelSchedule> result = new java.util.concurrent.ConcurrentHashMap<>();

        requests.parallelStream().forEach(req -> {
            String reqId = req.requestId;
            String criteria = req.criteria == null ? "Time" : req.criteria;

            if (req.source.equals(req.destination)) {
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, "Not generated"));
                return;
            }

            List<Integer> starts = departuresFrom.getOrDefault(req.source, new ArrayList<>());

            if (starts.isEmpty()) {
                String summary = generateSummary ? "No routes available" : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, summary));
                return;
            }

            Comparator<State> comp = getComparator(criteria);
            PriorityQueue<State> pq = new PriorityQueue<>(comp);

            for (int si : starts) {
                ScheduleRecord s = idxToSchedule.get(si);
                long dep = s.departure;
                long arr = s.arrivalAdjusted();
                java.util.BitSet used = new java.util.BitSet(schedules.size());
                used.set(si);
                State st = new State(si, si, dep, arr, s.cost, 1, null, used);
                pq.add(st);
            }

            State best = null;
            java.util.Set<Long> visitedSignatures = new java.util.HashSet<>();
            final int MAX_HOPS_LOCAL = 4; 
            final int MAX_EXPANSIONS_LOCAL = 1000;

            Map<Integer, List<long[]>> bestSignatures = new HashMap<>();
            final int MAX_LABELS_PER_NODE_LOCAL = 1;


            int expansions = 0;
            while (!pq.isEmpty()) {
                State cur = pq.poll();

                if (++expansions > MAX_EXPANSIONS_LOCAL) break; 
                if (best != null && comp.compare(cur, best) >= 0) break;
                if (cur.hops > MAX_HOPS_LOCAL) continue;

                ScheduleRecord lastRec = idxToSchedule.get(cur.lastIdx);
                if (lastRec.destination.equals(req.destination)) {
                    if (best == null || comp.compare(cur, best) < 0) {
                        best = cur;
                    }
                    continue;
                }

                List<Integer> nextList = departuresFrom.getOrDefault(lastRec.destination, new ArrayList<>());
                for (int ni : nextList) {
                    ScheduleRecord nextRec = idxToSchedule.get(ni);

                    boolean already = cur.usedContains(ni);
                    if (already) continue;

                    long baseDep = nextRec.departure;
                    long baseArr = nextRec.arrival;
                    long candidateDep = baseDep;
                    long prevArr = cur.arrivalAbs;
                    if (candidateDep < (prevArr % 1440)) {
                        long k = (prevArr - candidateDep + 1439) / 1440; 
                        candidateDep = candidateDep + k * 1440;
                    } else {
                        long dayOffset = (prevArr / 1440) * 1440;
                        candidateDep = candidateDep + dayOffset;
                        if (candidateDep < prevArr) candidateDep += 1440;
                    }

                    long candidateArr = candidateDep + ((baseArr >= baseDep) ? (baseArr - baseDep) : (baseArr + 1440 - baseDep));
                    java.util.BitSet nUsed = (java.util.BitSet) cur.usedIndices.clone();
                    nUsed.set(ni);
                    State nxt = new State(cur.startIdx, ni, cur.firstDepartureAbs, candidateArr, cur.totalCost + nextRec.cost, cur.hops + 1, cur, nUsed);

                    long sig = (((long) ni) << 48) ^ (candidateArr & 0x0000FFFFFFFFFFFFL) ^ (((long) nxt.hops) << 40);
                    if (visitedSignatures.contains(sig)) continue;

                    long[] curSig = new long[] { candidateArr, nxt.totalCost, nxt.hops };
                    List<long[]> list = bestSignatures.get(ni);
                    if (isDominatedPrimitive(list, curSig)) continue;

                    if (list == null) list = new ArrayList<>();
                    List<long[]> keep = new ArrayList<>();
                    for (long[] s : list) {
                        if (!dominatesPrimitive(curSig, s)) keep.add(s);
                    }
                    keep.add(curSig);
                    if (keep.size() > MAX_LABELS_PER_NODE_LOCAL) {
                        int worstIdx = 0;
                        for (int i = 1; i < keep.size(); i++) {
                            if (compareSignaturesPrimitive(keep.get(i), keep.get(worstIdx), criteria) > 0) worstIdx = i;
                        }
                        keep.remove(worstIdx);
                    }
                    bestSignatures.put(ni, keep);

                    visitedSignatures.add(sig);
                    pq.add(nxt);
                }
            }

            if (best == null) {
                String summary = generateSummary ? "No routes available" : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, summary));
            } else {
                List<Route> routes = new ArrayList<>();
                State cur = best;
                while (cur != null) {
                    if (cur.lastIdx >= 0) {
                        ScheduleRecord sr = idxToSchedule.get(cur.lastIdx);
                        if (sr != null) routes.add(0, sr.toRoute());
                    }
                    cur = cur.parent;
                }
                long primaryValue = computePrimaryValue(best, criteria);
                String summary = generateSummary ? generateSummaryText(routes, criteria) : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(routes, criteria, primaryValue, summary));
            }
        });

        return result;
    }

    private Comparator<State> getComparator(String criteria) {
        String c = criteria == null ? "time" : criteria.toLowerCase();
        switch (c) {
            case "cost":
                return (a, b) -> {
                    if (a.totalCost != b.totalCost) return Long.compare(a.totalCost, b.totalCost);
                    long at = a.arrivalAbs - a.firstDepartureAbs;
                    long bt = b.arrivalAbs - b.firstDepartureAbs;
                    if (at != bt) return Long.compare(at, bt);
                    return Integer.compare(a.hops, b.hops);
                };
            case "hops":
                return (a, b) -> {
                    if (a.hops != b.hops) return Integer.compare(a.hops, b.hops);
                    long at = a.arrivalAbs - a.firstDepartureAbs;
                    long bt = b.arrivalAbs - b.firstDepartureAbs;
                    if (at != bt) return Long.compare(at, bt);
                    return Long.compare(a.totalCost, b.totalCost);
                };
            default:
                return (a, b) -> {
                    long at = a.arrivalAbs - a.firstDepartureAbs;
                    long bt = b.arrivalAbs - b.firstDepartureAbs;
                    if (at != bt) return Long.compare(at, bt);
                    if (a.totalCost != b.totalCost) return Long.compare(a.totalCost, b.totalCost);
                    return Integer.compare(a.hops, b.hops);
                };
        }
    }

    private long computePrimaryValue(State s, String criteria) {
        String c = criteria == null ? "time" : criteria.toLowerCase();
        switch (c) {
            case "cost":
                return s.totalCost;
            case "hops":
                return s.hops;
            default:
                return s.arrivalAbs - s.firstDepartureAbs;
        }
    }

    private String generateSummaryText(List<Route> path, String criteria) {
        String apiKey = System.getenv("HF_API_KEY");
        String prompt = buildPromptFromPath(path, criteria);
        if (apiKey == null || apiKey.isEmpty()) {
            long duration = 0;
            if (path != null && !path.isEmpty()) {
                try {
                    long start = parseTime(path.get(0).getDepartureTime());
                    long end = parseTime(path.get(path.size()-1).getArrivalTime());
                    duration = end >= start ? (end - start) : (end + 1440 - start);
                } catch (Exception ex) { duration = 0; }
            }
            return "Total travel time " + duration + " minutes. Optimal by " + criteria + ".";
        }

        try {
            String json = "{\"inputs\":\"" + prompt.replace("\"", "\\\"").replace("\n", "\\n") + "\",\"options\":{\"wait_for_model\":true}}";
            URL url = new URL("https://api-inference.huggingface.co/models/facebook/bart-large-cnn");
            HttpURLConnection conn = (HttpURLConnection) url.openConnection();
            try {
                conn.setRequestMethod("POST");
                conn.setRequestProperty("Authorization", "Bearer " + apiKey);
                conn.setRequestProperty("Content-Type", "application/json; charset=UTF-8");
                conn.setDoOutput(true);
                try (OutputStream os = conn.getOutputStream(); OutputStreamWriter osw = new OutputStreamWriter(os, StandardCharsets.UTF_8)) {
                    osw.write(json);
                    osw.flush();
                }

                int code = conn.getResponseCode();
                if (code == 200) {
                    StringBuilder sb = new StringBuilder();
                    try (BufferedReader br = new BufferedReader(new InputStreamReader(conn.getInputStream(), StandardCharsets.UTF_8))) {
                        String line;
                        while ((line = br.readLine()) != null) sb.append(line).append('\n');
                    }
                    String text = sb.toString();
                    String summary = extractSummaryFromResponse(text);
                    if (summary != null && !summary.isEmpty()) return summary.length() > 300 ? summary.substring(0, 300) : summary;
                    return text.length() > 300 ? text.substring(0, 300) : text;
                }
            } finally {
                conn.disconnect();
            }
        } catch (Exception ex) {
            // ignore and fallback
        }
        long duration = 0;
        if (path != null && !path.isEmpty()) {
            try {
                long start = parseTime(path.get(0).getDepartureTime());
                long end = parseTime(path.get(path.size()-1).getArrivalTime());
                duration = end >= start ? (end - start) : (end + 1440 - start);
            } catch (Exception ex) { duration = 0; }
        }
        return "Total travel time " + duration + " minutes. Optimal by " + criteria + ".";
    }

    private String buildPromptFromPath(List<Route> path, String criteria) {
        StringBuilder sb = new StringBuilder();
        sb.append("You are a travel assistant. Provide a one-sentence (<=60 words) summary for this itinerary. Criteria: ").append(criteria).append(".\n");
        sb.append("Legs:\n");
        if (path != null) {
            for (Route r : path) {
                sb.append(r.getSource()).append("->").append(r.getDestination()).append(" (")
                        .append(r.getDepartureTime()).append("-").append(r.getArrivalTime()).append(")\n");
            }
        }
        return sb.toString();
    }

    private List<ScheduleRecord> readSchedules(Path p) throws IOException {
        List<String> lines = Files.readAllLines(p);
        List<ScheduleRecord> out = new ArrayList<>();
        for (int i = 1; i < lines.size(); i++) {
            String ln = lines.get(i).trim();
            if (ln.isEmpty()) continue;
            String[] parts = ln.split(",");
            if (parts.length < 6) continue;
            String src = parts[0];
            String dst = parts[1];
            String mode = parts[2];
            String dep = parts[3];
            String arr = parts[4];
            long cost;
            try { cost = Long.parseLong(parts[5]); } catch (Exception ex) { cost = 0L; }
            out.add(new ScheduleRecord(src, dst, mode, dep, arr, cost));
        }
        return out;
    }

    private List<CustomerRequest> readRequests(Path p) throws IOException {
        List<String> lines = Files.readAllLines(p);
        List<CustomerRequest> out = new ArrayList<>();
        for (int i = 1; i < lines.size(); i++) {
            String ln = lines.get(i).trim();
            if (ln.isEmpty()) continue;
            String[] parts = ln.split(",");
            if (parts.length < 5) continue;
            out.add(new CustomerRequest(parts[0], parts[1], parts[2], parts[3], parts[4]));
        }
        return out;
    }

    static class ScheduleRecord {
        String source;
        String destination;
        String mode;
        String departureTime;
        String arrivalTime;
        long departure; 
        long arrival;
        long cost;

        ScheduleRecord(String s, String d, String m, String dep, String arr, long cost) {
            this.source = s; this.destination = d; this.mode = m; this.departureTime = dep; this.arrivalTime = arr; this.cost = cost;
            this.departure = parseTime(dep);
            this.arrival = parseTime(arr);
        }

        long arrivalAdjusted() {
            if (arrival >= departure) return arrival;
            return arrival + 1440;
        }

        Route toRoute() {
            return new Route(source, destination, mode, departureTime, arrivalTime);
        }
    }

    static class CustomerRequest {
        String requestId;
        String customerName;
        String source;
        String destination;
        String criteria;

        CustomerRequest(String id, String name, String s, String d, String c) {
            this.requestId = id;
            this.customerName = name;
            this.source = s;
            this.destination = d;
            this.criteria = c;
        }
    }

    static class State {
        int startIdx;
        int lastIdx;
        long firstDepartureAbs;
        long arrivalAbs;
        long totalCost;
    int hops;
    State parent;
    java.util.BitSet usedIndices;

        State(int startIdx, int lastIdx, long firstDepartureAbs, long arrivalAbs, long totalCost, int hops, State parent, java.util.BitSet usedIndices) {
            this.startIdx = startIdx; this.lastIdx = lastIdx; this.firstDepartureAbs = firstDepartureAbs; this.arrivalAbs = arrivalAbs; this.totalCost = totalCost; this.hops = hops; this.parent = parent; this.usedIndices = usedIndices;
        }

        boolean usedContains(int idx) {
            return usedIndices.get(idx);
        }
    }

    private static boolean isDominatedPrimitive(List<long[]> list, long[] s) {
        if (list == null) return false;
        for (long[] e : list) {
            if (e[0] <= s[0] && e[1] <= s[1] && e[2] <= s[2]) return true;
        }
        return false;
    }

    private static boolean dominatesPrimitive(long[] a, long[] b) {
        boolean noWorse = a[0] <= b[0] && a[1] <= b[1] && a[2] <= b[2];
        boolean strictlyBetter = a[0] < b[0] || a[1] < b[1] || a[2] < b[2];
        return noWorse && strictlyBetter;
    }

    private static int compareSignaturesPrimitive(long[] a, long[] b, String criteria) {
        String c = criteria == null ? "time" : criteria.toLowerCase();
        switch (c) {
            case "cost":
                if (a[1] != b[1]) return Long.compare(a[1], b[1]);
                if (a[0] != b[0]) return Long.compare(a[0], b[0]);
                return Long.compare(a[2], b[2]);
            case "hops":
                if (a[2] != b[2]) return Long.compare(a[2], b[2]);
                if (a[0] != b[0]) return Long.compare(a[0], b[0]);
                return Long.compare(a[1], b[1]);
            default:
                if (a[0] != b[0]) return Long.compare(a[0], b[0]);
                if (a[1] != b[1]) return Long.compare(a[1], b[1]);
                return Long.compare(a[2], b[2]);
        }
    }

    private static long parseTime(String t) {
        try {
            String[] p = t.split(":");
            int hh = Integer.parseInt(p[0]);
            int mm = Integer.parseInt(p[1]);
            return hh * 60L + mm;
        } catch (Exception ex) { return 0; }
    }

    private static String extractSummaryFromResponse(String respBody) {
        if (respBody == null || respBody.isEmpty()) return null;
        String lower = respBody;
        int idx = lower.indexOf("\"summary_text\"");
        if (idx >= 0) {
            int colon = lower.indexOf(':', idx);
            if (colon >= 0) {
                int firstQuote = lower.indexOf('"', colon);
                if (firstQuote >= 0) {
                    int secondQuote = lower.indexOf('"', firstQuote + 1);
                    if (secondQuote > firstQuote) {
                        return unescapeJsonString(lower.substring(firstQuote + 1, secondQuote));
                    }
                }
            }
        }
        idx = lower.indexOf("\"generated_text\"");
        if (idx >= 0) {
            int colon = lower.indexOf(':', idx);
            if (colon >= 0) {
                int firstQuote = lower.indexOf('"', colon);
                if (firstQuote >= 0) {
                    int secondQuote = lower.indexOf('"', firstQuote + 1);
                    if (secondQuote > firstQuote) {
                        return unescapeJsonString(lower.substring(firstQuote + 1, secondQuote));
                    }
                }
            }
        }
        String trimmed = respBody.trim();
        if (trimmed.startsWith("[")) trimmed = trimmed.substring(1);
        if (trimmed.endsWith("]")) trimmed = trimmed.substring(0, trimmed.length()-1);
        if (trimmed.startsWith("{")) trimmed = trimmed.substring(1);
        if (trimmed.endsWith("}")) trimmed = trimmed.substring(0, trimmed.length()-1);
        trimmed = trimmed.replaceAll("\\\\n", " ").replaceAll("\\\\r", " ");
        return !trimmed.isEmpty() ? trimmed : null;
    }

    private static String unescapeJsonString(String s) {
        return s.replaceAll("\\\\\"", "\"")
                .replaceAll("\\\\n", " ")
                .replaceAll("\\\\r", " ")
                .replaceAll("\\\\t", " ");
    }
}
