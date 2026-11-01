#include <stdio.h>
int points(const char* const games[10]){
  int tally = 0;
  int i;
  for (i=0; i<=9; i++){
    int x = games[i][0];
    int y = games[i][2];
    if (x>y){
      tally += 3;
    }
    else if (x==y){
      tally += 1;
    }
    else{
        continue;
      }
  }
return tally;
}