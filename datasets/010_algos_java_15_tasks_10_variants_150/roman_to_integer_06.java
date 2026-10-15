class Solution {
    public int romanToInt(String s) {
        Map<Character, Integer> map = Map.of(
            'I', 1,
            'V', 5,
            'X', 10,
            'L', 50,
            'C', 100,
            'D', 500,
            'M', 1000
        );

        int ans = 0;
        int n = s.length();

        for (int i = 0; i < n; i++) {
            int value = map.get(s.charAt(i));
            
            // Check if the next character has a larger value
            if (i + 1 < n && value < map.get(s.charAt(i + 1))) {
                // If it does, subtract this value (e.g., IV = -1 + 5)
                ans -= value;
            } else {
                // Otherwise, add it
                ans += value;
            }
        }

        return ans;
    }
}