class Solution {
    int getNum(String s, int i, long result, int sign){
        if(i >= s.length() || !Character.isDigit(s.charAt(i))) return sign * (int) result;
        result = result * 10 + (s.charAt(i) - '0');

        if (sign * result >= Integer.MAX_VALUE) return Integer.MAX_VALUE;
        if (sign * result <= Integer.MIN_VALUE) return Integer.MIN_VALUE;
        
        return getNum(s, i+1, result, sign);
    }

    public int myAtoi(String s) {
        s = s.trim();
        if (s == null || s.isEmpty()) return 0;
        int i = 0, sign = 1;
        if (s.charAt(i) == '-' || s.charAt(i) == '+') {
            sign = (s.charAt(i) == '-') ? -1 : 1;
            i++;
        }

        while(i < s.length() && s.charAt(i) == '0') i++;
        
        return getNum(s, i, 0L, sign);
    }
}