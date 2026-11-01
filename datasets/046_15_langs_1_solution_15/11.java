public class TotalPoints {
  
    public static int points(String[] games) {
        int sum = 0;
        
        for (String s : games) {
          char x = s.charAt(0),
               y = s.charAt(2);
          
          sum += x > y ? 3 : x == y ? 1 : 0;
        }
        
        return sum;
    }
}