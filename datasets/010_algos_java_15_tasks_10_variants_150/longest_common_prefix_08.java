class Solution {
    public String longestCommonPrefix(String[] strs) {

        String pre = "";
        int pos = 0;

        int minLen = Integer.MAX_VALUE;
        for (String word : strs) {
            minLen = Math.min(minLen, word.length());
        }

        while (pos < minLen) {

            char current = strs[0].charAt(pos);

            for (int i = 1; i < strs.length; i++) {
                if (strs[i].charAt(pos) != current) {
                    return pre;
                }
            }

            pre += current;
            pos++;
        }

        return pre;
    }
}