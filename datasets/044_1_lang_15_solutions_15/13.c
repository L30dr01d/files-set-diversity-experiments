#include <stdio.h>

int points(const char* const games[10]) {
    int point = 0;
    int x, y;
    for (int i = 0; i < 10; i++) {
        sscanf(games[i], "%d:%d", &x, &y);
        if (x > y) {
          point += 3;
        } else if (x == y) {
          point++;
        }
    }
  return point;
}