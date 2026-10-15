class Solution {
    public String longestCommonPrefix(String[] strs) {
        Arrays.sort(strs);
        String s = "";
        int i = 0;
        int length = strs.length;

        while (i < strs[0].length()) {
            if (strs[0].charAt(i) == strs[length - 1].charAt(i))
                s += strs[0].charAt(i);
            else
                break;
            i++;
        }

        return s;
    }
}