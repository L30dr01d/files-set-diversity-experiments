class Solution {

    private final int[] val = {
        1000, 900, 500, 400,
        100, 90, 50, 40,
        10, 9, 5, 4, 1
    };

    private final String[] sym = {
        "M", "CM", "D", "CD",
        "C", "XC", "L", "XL",
        "X", "IX", "V", "IV", "I"
    };

    public int romanToInt(String s) {

        int result = 0;
        int i = 0;

        while (s.length() > 0) {

            if (s.startsWith(sym[i])) {
                result += val[i];
                s = s.substring(sym[i].length());
            } else {
                i++;
            }
        }

        return result;
    }
}