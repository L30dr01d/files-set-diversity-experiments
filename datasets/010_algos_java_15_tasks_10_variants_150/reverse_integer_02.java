class Solution {
    public int reverse(int x) {
    
      
       int ans=0;
       
       while(x!=0){
            //extract last digit
            int digit=x%10;
            //OverFlow Check
             if (ans > Integer.MAX_VALUE / 10 || (ans == Integer.MAX_VALUE / 10 && digit > 7)) return 0;

            // Underflow check
            if (ans < Integer.MIN_VALUE / 10 || (ans == Integer.MIN_VALUE / 10 && digit < -8)) return 0;
            
            
            ans =(ans*10)+digit;
            //remove last digit
            x=x/10;
       }

        return ans;
    }
}