#include <stdlib.h>

int points(char* games[]) {

    // <---- hajime!
    int sum = 0;
    for(int i = 0; i < 10; i++) {
      if(games[i][0] > games[i][2])
        sum += 3;
      else if(games[i][0] == games[i][2])
        sum += 1;
    }
    return sum;

}