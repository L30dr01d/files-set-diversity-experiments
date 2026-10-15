class Solution {
    public int lengthOfLongestSubstring(String s) {
        int n = s.length();
        int res = 0;
        for (int i = 0; i < n; i++) {
            Set<Character> charSet = new HashSet<>();
            for (int j = i; j < n; j++) {
                if (charSet.contains(s.charAt(j))) {
                    break;
                } else {
                    charSet.add(s.charAt(j));
                    res = Math.max(res, j - i + 1);
                }
            }
        }
        return res;
    }
}