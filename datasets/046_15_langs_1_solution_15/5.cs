using System.Linq;
using System;
public static class Kata {
    public static int TotalPoints(string[] games) {
        int total = 0;
        foreach (string game in games) {
          if (game[0] > game[2])
            total += 3;
          else if (game[0] == game[2])
            total += 1;            
        }
        return total;
    }
}