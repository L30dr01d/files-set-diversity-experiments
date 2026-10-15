class Solution {
    public List<List<Integer>> threeSum(int[] nums) {
         Arrays.sort(nums);

         List<List<Integer>> ans = new ArrayList<>();
         int j = 1, k = 2, rSum;

         for(int i = 0; i < nums.length; i++){

            j = i + 1;
            k = nums.length - 1;

            if(i > 0 && nums[i] == nums[i - 1]) continue;

            rSum = -nums[i];

            while(j < k){

                if(nums[j] + nums[k] == rSum){

                    List<Integer> sum = new ArrayList<>();

                    sum.add(nums[i]);
                    sum.add(nums[j]);
                    sum.add(nums[k]);

                    ans.add(sum);

                    j++;
                    k--;

                    while(j < k && nums[j] == nums[j - 1]){
                        j++;
                    }

                    while(j < k && nums[k] == nums[k + 1]){
                        k--;
                    }
                }

                else if(nums[j] + nums[k] > rSum){
                    k--;
                }

                else{
                    j++;
                }
            }
         }

       return ans;
    }
}