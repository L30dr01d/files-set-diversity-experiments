#include <stdint.h>

typedef int_fast32_t num;

int32_t points(char* game[]) {
  enum team { X = 0, Y = 2 };
  num sum = 0;
  
  for (num i = 0; i < 10; i++) {
    if (game[i][X] > game[i][Y]) {
      sum += 3;
    } else if (game[i][X] == game[i][Y]) {
      sum += 1;
    }
  }
  return sum;
}