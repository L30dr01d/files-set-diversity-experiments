#include <stdlib.h>

int points(char* games[])
{
  int sum = 0;
  for (int i = 0; i < 10; i++)
    sum += games[i][0] > games[i][2] ? 3
         : games[i][0] < games[i][2] ? 0
         : 1;
  return sum;
}