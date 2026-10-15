class Solution {
    public static int helper(String s, int i, long num, int sign){
        if(i>=s.length() || !Character.isDigit(s.charAt(i))){
            return (int)(num * sign);
        }

        num = num*10 + (s.charAt(i) - '0');

        if(num*sign <= Integer.MIN_VALUE) return Integer.MIN_VALUE;
        if(num*sign >= Integer.MAX_VALUE) return Integer.MAX_VALUE;

        return helper(s, i+1, num, sign);
    }
    public int myAtoi(String s) {
        int i=0;

        while(i<s.length() && s.charAt(i)==' '){
            i++;
        }

        int sign = 1;
        if(i<s.length() && (s.charAt(i)=='+' || s.charAt(i)=='-')){
            if(s.charAt(i)=='-'){
                sign = -1;
            }
            else{
                sign = 1;
            }
            i++;
        }

        return helper(s, i, 0, sign);
    }
}