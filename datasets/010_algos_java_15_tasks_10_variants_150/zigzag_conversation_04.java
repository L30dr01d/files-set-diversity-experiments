class Solution {
    public String convert(String s, int numRows) {
        int n = s.length();
        if (numRows == 1 || n == numRows)
            return s;
        StringBuilder[] arr = new StringBuilder[numRows];
        int curr = 0;
        boolean rev = false;
        for (int i = 0; i < numRows; i++)
            arr[i] = new StringBuilder();
        for (int i = 0; i < n; i++) {
            arr[curr].append(s.charAt(i));
            if (curr == numRows - 1)
                rev = true;
            else if (curr == 0)
                rev = false;
            curr += rev ? -1 : 1;
        }
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < numRows; i++)
            sb.append(arr[i].toString());
        return sb.toString();
    }
}
