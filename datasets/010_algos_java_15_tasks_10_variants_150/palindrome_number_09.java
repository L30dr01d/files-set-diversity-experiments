class Solution {
    public boolean isPalindrome(int x) {
        int store = 0;
        int temp = x;

        if(x < 0){
            return false;
        }
        
        while(temp != 0){
            int digit = temp%10;
            store = store*10 + digit;
            temp /= 10;
        }

        if(store == x){
            return true;
        }
        return false;
    }
}