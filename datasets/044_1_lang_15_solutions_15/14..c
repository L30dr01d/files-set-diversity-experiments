int points(const char* const games[10]) {
    int p = 0;
    for(int i = 0; i < 10 ; i++){
      int x, y;
      sscanf(games[i], "%d:%d", &x, &y);
      p += (x==y)? 1 : (x > y) ? 3 : 0;
    }
    return p;
}