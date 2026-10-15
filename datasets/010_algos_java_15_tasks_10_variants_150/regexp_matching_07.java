class Solution {
    int[][] dp;

    public boolean solve(String txt, String pat, int i, int j) {
        if (i == pat.length())
            return j == txt.length();

        if (dp[i][j] != -1)
            return dp[i][j] == 1;

        boolean isMatch = (j < txt.length() &&
                          (pat.charAt(i) == txt.charAt(j) || pat.charAt(i) == '.'));

        boolean res;

        if (i + 1 < pat.length() && pat.charAt(i + 1) == '*') {
            res = solve(txt, pat, i + 2, j) ||
                  (isMatch && solve(txt, pat, i, j + 1));
        } else {
            res = isMatch && solve(txt, pat, i + 1, j + 1);
        }

        dp[i][j] = res ? 1 : 0;
        return res;
    }

    public boolean isMatch(String s, String p) {
        int n = p.length(), m = s.length();
        dp = new int[n + 1][m + 1];

        for (int[] row : dp)
            Arrays.fill(row, -1);

        return solve(s, p, 0, 0);
    }
}