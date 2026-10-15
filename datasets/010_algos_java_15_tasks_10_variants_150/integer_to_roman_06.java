class Solution {
    private static final String[] THOUSANDS = { "", "M", "MM", "MMM" };
    private static final String[] HUNDREDS = { "", "C", "CC", "CCC", "CD", "D", "DC", "DCC", "DCCC", "CM" };
    private static final String[] TENS = { "", "X", "XX", "XXX", "XL", "L", "LX", "LXX", "LXXX", "XC" };
    private static final String[] ONES = { "", "I", "II", "III", "IV", "V", "VI", "VII", "VIII", "IX" };

    public String intToRoman(int num) {

        return new StringBuilder().append(THOUSANDS[num / 1000])
                .append(HUNDREDS[(num / 100) % 10])
                .append(TENS[(num / 10) % 10])
                .append(ONES[num % 10])
                .toString();
    }
}