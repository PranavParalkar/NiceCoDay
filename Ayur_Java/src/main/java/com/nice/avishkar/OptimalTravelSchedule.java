package com.nice.avishkar;

import java.util.List;

public class OptimalTravelSchedule {
    List<Route> routes;

    String criteria;

    long value;

    String summary;

    public OptimalTravelSchedule(List<Route> routes, String criteria, long value, String summary) {
        this.routes = routes;
        this.criteria = criteria;
        this.value = value;
        this.summary = summary;
    }

    public List<Route> getRoutes() {
        return routes;
    }

    public void setRoutes(List<Route> routes) {
        this.routes = routes;
    }

    public String getCriteria() {
        return criteria;
    }


    public void setCriteria(String criteria) {
        this.criteria = criteria;
    }

    public long getValue() {
        return value;
    }

    public void setValue(long value) {
        this.value = value;
    }

    public String getSummary() {
        return summary;
    }

    public void setSummary(String summary) {
        this.summary = summary;
    }
}
