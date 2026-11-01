#include <stdlib.h>

int points(char* games[]) {

    int points = 0; 
    int x, y;
    
    for (int i = 0; i < 10; i++)
    {
      sscanf(games[i], "%d:%d", &x, &y);

      if (x > y) points += 3;
      else if (x == y) points += 1;
    }
   
    return points;
}