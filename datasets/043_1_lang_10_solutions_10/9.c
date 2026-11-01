int points(const char* const games[10]) {
    int sum = 0;
    for(int i=0; i<10; i++){
        int x, y;
        sscanf(games[i], "%d:%d", &x, &y);
        if( x == y ) sum += 1;
        if( x > y ) sum += 3;
    }
    return sum;
}