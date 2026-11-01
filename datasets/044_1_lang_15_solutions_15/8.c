#include <stdlib.h>

int points(char* a[]) {
  int r = 0;
  for (int i = 0; i < 10; i++) r += (a[i][0] >= a[i][2]) + (a[i][0] > a[i][2]) * 2;
  return r;
}