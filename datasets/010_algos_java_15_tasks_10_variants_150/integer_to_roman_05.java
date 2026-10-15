class Solution {
    public String intToRoman(int num) {
        int[] no={1000,900,500,400,100,90,50,40,10,9,5,4,1};
        String[] sym={"M","CM","D","CD","C","XC","L","XL","X","IX","V","IV","I"};
        String result="";
         for (int i = 0; i < no.length; i++) {
            while (num >= no[i]) {
                result += sym[i];
                num -= no[i];
            }
        }

        return result;
    }
}