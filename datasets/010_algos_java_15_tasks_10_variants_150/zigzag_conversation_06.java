class Solution {
    public String convert(String s, int numRows) {
        // optimal, without using extra space
        int n = s.length();
        if (numRows == 1 || numRows >= n) {
            return s;
        }
        int cycle = 2 * numRows - 2;
        StringBuilder ans = new StringBuilder();
        for (int row = 0; row < numRows; row++) {
            for (int j = 0; j + row < n; j += cycle) {
                ans.append(s.charAt(j + row));
                if (row > 0 && row < numRows - 1 && j + cycle - row < n) {
                    ans.append(s.charAt(j + cycle - row));
                }
            }
        }
        return ans.toString();
    }
}