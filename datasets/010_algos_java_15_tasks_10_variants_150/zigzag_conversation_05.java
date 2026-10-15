class Solution {
    public String convert(String s, int numRows) {
        if (numRows == 1 || numRows >= s.length()) return s;

        int n = s.length();
        int cycle = 2 * (numRows - 1);
        char[] result = new char[n];
        int idx = 0;

        for (int row = 0; row < numRows; row++) {
            for (int j = row; j < n; j += cycle) {
                result[idx++] = s.charAt(j);
                int diag = j + cycle - 2 * row;
                if (row != 0 && row != numRows - 1 && diag < n) {
                    result[idx++] = s.charAt(diag);
                }
            }
        }
        return new String(result);
    }
}