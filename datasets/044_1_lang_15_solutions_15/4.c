#include <stdlib.h>

int points(char* games[]) {
  int p = 0;
  for (int i = 0; i < 10; ++i) {
    int x = games[i][0] - '0';
    int y = games[i][2] - '0';
    p += (x > y) * 3 + (x == y);
  }
  return p;
}