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
import java.util.HashSet;
import java.util.List;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.Comparator;



public class TravelOptimizerImpl implements ITravelOptimizer {

    private final boolean generateSummary;

    TravelOptimizerImpl(boolean generateSummary)
    {
        this.generateSummary = generateSummary;
    }

    public Map<String, OptimalTravelSchedule> getOptimalTravelOptions(ResourceInfo resourceInfo) throws IOException {
        // Read schedules and customer requests
        List<ScheduleRecord> schedules = readSchedules(resourceInfo.getTransportSchedulePath());
        List<CustomerRequest> requests = readRequests(resourceInfo.getCustomerRequestPath());

        // index schedules
        Map<Integer, ScheduleRecord> idxToSchedule = new HashMap<>();
        for (int i = 0; i < schedules.size(); i++) idxToSchedule.put(i, schedules.get(i));

        // build adjacency of schedule indices by source -> list
        Map<String, List<Integer>> departuresFrom = new HashMap<>();
        for (int i = 0; i < schedules.size(); i++) {
            departuresFrom.computeIfAbsent(schedules.get(i).source, k -> new ArrayList<>()).add(i);
        }

        Map<String, OptimalTravelSchedule> result = new HashMap<>();

        for (CustomerRequest req : requests) {
            String reqId = req.requestId;
            String criteria = req.criteria == null ? "Time" : req.criteria;

            // trivial same-source-destination
            if (req.source.equals(req.destination)) {
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, "Not generated"));
                continue;
            }

            // prepare start trip indices
            List<Integer> starts = departuresFrom.getOrDefault(req.source, new ArrayList<>());

            // if no starting trips -> no route
            if (starts.isEmpty()) {
                String summary = generateSummary ? "No routes available" : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, summary));
                continue;
            }

            // priority queue of states
            Comparator<State> comp = getComparator(criteria);
            PriorityQueue<State> pq = new PriorityQueue<>(comp);

            // initialize
            for (int si : starts) {
                ScheduleRecord s = idxToSchedule.get(si);
                long dep = s.departure;
                long arr = s.arrivalAdjusted();
                State st = new State(si, si, dep, arr, s.cost, 1, new ArrayList<>());
                st.path.add(s.toRoute());
                pq.add(st);
            }

            State best = null;
            Set<String> visitedSignatures = new HashSet<>();
            final int MAX_HOPS = 6; // pragmatic cap to avoid explosion; covers most realistic itineraries

            // BFS/Dijkstra with state including absolute times. Limit path length to schedules size to avoid cycles.
            while (!pq.isEmpty()) {
                State cur = pq.poll();

                // pruning: avoid overly long paths
                if (cur.hops > MAX_HOPS) continue;

                ScheduleRecord lastRec = idxToSchedule.get(cur.lastIdx);

                // if reached destination
                if (lastRec.destination.equals(req.destination)) {
                    if (best == null || comp.compare(cur, best) < 0) {
                        best = cur;
                    }
                    // continue searching because equal primary might have better tie-breakers
                    continue;
                }

                // expand outgoing trips from current location
                List<Integer> nextList = departuresFrom.getOrDefault(lastRec.destination, new ArrayList<>());
                for (int ni : nextList) {
                    ScheduleRecord nextRec = idxToSchedule.get(ni);

                    // avoid reusing the same schedule record in path (simple cycle prevention)
                    boolean already = cur.usedContains(ni);
                    if (already) continue;

                    // compute next departure absolute >= cur.arrival
                    long baseDep = nextRec.departure;
                    long baseArr = nextRec.arrival;
                    long candidateDep = baseDep;
                    long prevArr = cur.arrivalAbs;
                    if (candidateDep < (prevArr % 1440)) {
                        // need to shift forward by at least one day relative to prevArr
                        long k = (prevArr - candidateDep + 1439) / 1440; // ceil
                        candidateDep = candidateDep + k * 1440;
                    } else {
                        // candidateDep base might be >= prevArr%1440 but actual prevArr could be in later day
                        long dayOffset = (prevArr / 1440) * 1440;
                        candidateDep = candidateDep + dayOffset;
                        if (candidateDep < prevArr) candidateDep += 1440;
                    }

                    long candidateArr = candidateDep + ((baseArr >= baseDep) ? (baseArr - baseDep) : (baseArr + 1440 - baseDep));

                    // build new state
                    State nxt = cur.copy();
                    nxt.lastIdx = ni;
                    nxt.arrivalAbs = candidateArr;
                    nxt.totalCost += nextRec.cost;
                    nxt.hops += 1;
                    nxt.path.add(nextRec.toRoute());
                    nxt.usedIndices.add(ni);

                    // signature to avoid repeating same (lastIdx, arrivalAbs modulo maybe 1440 and hops)
                    String sig = ni + "@" + (candidateArr % 1440) + "#" + nxt.hops;
                    if (visitedSignatures.contains(sig)) continue;
                    visitedSignatures.add(sig);

                    pq.add(nxt);
                }
            }

            if (best == null) {
                String summary = generateSummary ? "No routes available" : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(new ArrayList<>(), criteria, 0, summary));
            } else {
                long primaryValue = computePrimaryValue(best, criteria);
                String summary = generateSummary ? generateSummaryText(best, criteria) : "Not generated";
                result.put(reqId, new OptimalTravelSchedule(best.path, criteria, primaryValue, summary));
            }
        }

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

    private String generateSummaryText(State best, String criteria) {
        // try to call HuggingFace only if HF_API_KEY env set
        String apiKey = System.getenv("HF_API_KEY");
        String prompt = buildPromptFromState(best, criteria);
        if (apiKey == null || apiKey.isEmpty()) {
            // fallback short summary
            long duration = best.arrivalAbs - best.firstDepartureAbs;
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
        long duration = best.arrivalAbs - best.firstDepartureAbs;
        return "Total travel time " + duration + " minutes. Optimal by " + criteria + ".";
    }

    private String buildPromptFromState(State best, String criteria) {
        StringBuilder sb = new StringBuilder();
        sb.append("You are a travel assistant. Provide a one-sentence (<=60 words) summary for this itinerary. Criteria: ").append(criteria).append(".\n");
        sb.append("Legs:\n");
        for (Route r : best.path) {
            sb.append(r.getSource()).append("->").append(r.getDestination()).append(" (")
                    .append(r.getDepartureTime()).append("-").append(r.getArrivalTime()).append(")\n");
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

    // --- helper classes ---
    static class ScheduleRecord {
        String source;
        String destination;
        String mode;
        String departureTime;
        String arrivalTime;
        long departure; // minutes from 0
        long arrival; // minutes from 0
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
        List<Route> path;
        Set<Integer> usedIndices;

        State(int startIdx, int lastIdx, long firstDepartureAbs, long arrivalAbs, long totalCost, int hops, List<Route> path) {
            this.startIdx = startIdx; this.lastIdx = lastIdx; this.firstDepartureAbs = firstDepartureAbs; this.arrivalAbs = arrivalAbs; this.totalCost = totalCost; this.hops = hops; this.path = path;
            this.usedIndices = new HashSet<>();
            this.usedIndices.add(startIdx);
        }

        State copy() {
            List<Route> np = new ArrayList<>(this.path);
            State s = new State(this.startIdx, this.lastIdx, this.firstDepartureAbs, this.arrivalAbs, this.totalCost, this.hops, np);
            s.usedIndices = new HashSet<>(this.usedIndices);
            return s;
        }

        boolean usedContains(int idx) {
            return usedIndices.contains(idx);
        }

        // helper to allow marking used; we won't actually use usedContains logic to block by idx because mapping is complex
    }

    
    // removed unused helper classes

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
