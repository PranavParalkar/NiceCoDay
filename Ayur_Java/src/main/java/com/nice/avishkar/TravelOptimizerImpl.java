package com.nice.avishkar;


import java.io.IOException;
import java.util.Map;

public class TravelOptimizerImpl implements ITravelOptimizer {

    private boolean generateSummary;

    TravelOptimizerImpl(boolean generateSummary)
    {
        this.generateSummary = generateSummary;
    }

    public Map<String, OptimalTravelSchedule> getOptimalTravelOptions(ResourceInfo resourceInfo) throws IOException {
        // Your implementation will go here

        if(generateSummary)
        {
            // Generate and set the summary of each optimal travel option

        }
        return null; // Change this after implementation
    }
}
