class Solution {
    public boolean isMatch(String s, String p) {
        return match(s, p, 0, 0);
    }
    
    private boolean match(String s, String p, int sIndex, int pIndex) {
        if (sIndex == s.length() && pIndex == p.length()) {
            return true;
        }

        if (pIndex == p.length()) {
            return false;
        }
        
        char current_char = p.charAt(pIndex);
        boolean has_star = (pIndex + 1 < p.length() && p.charAt(pIndex + 1) == '*');
        
        if (has_star) {
            if (match(s, p, sIndex, pIndex + 2)) {
                return true;
            }
            
            int i = sIndex;
            while (i < s.length() && (current_char == '.' || s.charAt(i) == current_char)) {
                if (match(s, p, i + 1, pIndex + 2)) {
                    return true;
                }
                i++;
            }
            return false;
        } else {
            if (sIndex < s.length() && (current_char == '.' || s.charAt(sIndex) == current_char)) {
                return match(s, p, sIndex + 1, pIndex + 1);
            }
            return false;
        }
    }
}