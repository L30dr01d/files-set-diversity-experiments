class Solution {
    public String longestCommonPrefix(String[] strs) {
        // Base case: empty input
        if (strs == null || strs.length == 0)
            return "";

        // Assume the first string is the prefix
        String prefix = strs[0];

        // Compare the prefix with each string in the array
        for (int i = 1; i < strs.length; i++) {
            // While the current string doesn't start with the prefix
            while (strs[i].indexOf(prefix) != 0) {
                // Shorten the prefix from the end
                prefix = prefix.substring(0, prefix.length() - 1);

                // If empty, no common prefix exists across all strings
                if (prefix.isEmpty())
                    return "";
            }
        }

        return prefix;
    }
}