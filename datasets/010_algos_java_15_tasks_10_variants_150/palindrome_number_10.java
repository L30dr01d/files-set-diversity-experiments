class Solution {
    public boolean isPalindrome(int x) {
        int sum=0;
        int k=x;
        while(x>0){
        int rem=x%10;
        x/=10;
        sum=sum*10+rem;
        }
        if(k==sum){
            return true;
        }else{
            return false;
        }

        
        

        
    }
}