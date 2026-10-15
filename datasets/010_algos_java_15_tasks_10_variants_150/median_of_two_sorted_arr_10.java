class Solution {
    public double findMedianSortedArrays(int[] nums1, int[] nums2) {

        if (nums1.length > nums2.length) {
            return findMedianSortedArrays(nums2, nums1);
        }

        int n = nums1.length;
        int m = nums2.length;
        int totalLength = n + m;
        
        int half = (totalLength + 1)/2;
        int low = 0;
        int high = n;

        while (low <= high) {
            int cut1 = low + (high - low) / 2;
            
            int cut2 = half - cut1;

            int maxLeft1 = (cut1 == 0) ? Integer.MIN_VALUE : nums1[cut1 - 1];
            int minRight1 = (cut1 == n) ? Integer.MAX_VALUE : nums1[cut1];
            int maxLeft2 = (cut2 == 0) ? Integer.MIN_VALUE : nums2[cut2 - 1];
            int minRight2 = (cut2 == m) ? Integer.MAX_VALUE : nums2[cut2];

            if (maxLeft1 <= minRight2 && maxLeft2 <= minRight1) {
                if (totalLength % 2 == 0) {
                    return (Math.max(maxLeft1, maxLeft2) + Math.min(minRight1, minRight2)) / 2.0;
                } else {
                    return (double) Math.max(maxLeft1, maxLeft2);
                }
            } 
            else if (maxLeft1 > minRight2) {
                high = cut1 - 1;
            } else {
                low = cut1 + 1;
            }
        }
        
        return 0.0;
    }
}