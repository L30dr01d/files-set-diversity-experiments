class Solution {
    public int reverse(int x) {
        long sum = 0;
        while(x!=0){
            int rem = x%10;
            sum += rem;
           sum = sum*10;
            x= x/10;
        }
        sum = sum/10;
        if(sum > Integer.MAX_VALUE || sum<Integer.MIN_VALUE){
            return 0;
        }
        if(x<0){
            return (int)(-1*sum);
        }
        return (int)sum;
    }
}