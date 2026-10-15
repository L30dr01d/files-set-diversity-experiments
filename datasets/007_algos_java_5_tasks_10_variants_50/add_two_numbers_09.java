class Solution {
    public ListNode addTwoNumbers(ListNode l1, ListNode l2) {

        ListNode head = new ListNode(0);
        ListNode curr = head;

        int carry = 0;

        while(l1 != null || l2 != null || carry != 0)
        {
            int sum = carry;

            if(l1 != null) {
                sum += l1.val;
                l1 = l1.next;
            }

            if(l2 != null) {
                sum += l2.val;
                l2 = l2.next;
            }

            curr.next = new ListNode(sum % 10); 
            carry = sum / 10; 

            curr = curr.next;
        }

        return head.next;
    }
}