class Solution {
    public String convert(String s, int numRows) {
        // Trivial cases where zigzag does not change string.
        if (numRows == 1 || numRows >= s.length()) {
            return s;
        }

        List<StringBuilder> rows = new ArrayList<>();
        for (int i = 0; i < numRows; i++) {
            rows.add(new StringBuilder());
        }

        int idx = 0;  // current row
        int d = 1;    // +1 down, -1 up

        for (char ch : s.toCharArray()) {
            rows.get(idx).append(ch);

            if (idx == 0) {
                d = 1;         // turn downward at top
            } else if (idx == numRows - 1) {
                d = -1;        // turn upward at bottom
            }

            idx += d;
        }

        StringBuilder ans = new StringBuilder();
        for (StringBuilder row : rows) {
            ans.append(row);
        }
        return ans.toString();
    }
}