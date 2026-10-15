class Solution {
    public int lengthOfLongestSubstring(String s) {
        if(s.length() == 0){
            return 0;
        }
        HashMap<Character, Integer> map = new HashMap<>();
        int n = s.length();
        int maxLen = 0;

        for (int i = 0, j = 0; i < n; i++) {
            if (map.containsKey(s.charAt(i))) {
                j = Math.max(j, map.get(s.charAt(i)) + 1);
            }
            map.put(s.charAt(i), i);
            maxLen = Math.max(i - j + 1, maxLen);
        }
        return maxLen;
    }
}