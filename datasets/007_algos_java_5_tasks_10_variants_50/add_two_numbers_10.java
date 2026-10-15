class Solution {
    public ListNode addTwoNumbers(ListNode l1, ListNode l2) {
        return addTwoNumbersRecursive(l1, l2, 0);
    }

    private ListNode addTwoNumbersRecursive(ListNode l1, ListNode l2, int carry) {
        if (l1 == null && l2 == null && carry == 0) {
            return null;
        }

        int val1 = (l1 != null) ? l1.val : 0;
        int val2 = (l2 != null) ? l2.val : 0;
        int sum = val1 + val2 + carry;

        ListNode node = new ListNode(sum % 10);
        int newCarry = sum / 10;

        ListNode next1 = (l1 != null) ? l1.next : null;
        ListNode next2 = (l2 != null) ? l2.next : null;

        node.next = addTwoNumbersRecursive(next1, next2, newCarry);
        return node;
    }
}