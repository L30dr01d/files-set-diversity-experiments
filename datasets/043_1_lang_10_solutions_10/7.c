int points(const char* const games[10]) {

    // <---- hajime!
  int sum=0, i;
  for(i=0;i<10;i++)
  {
    if(games[i][0]>games[i][2])
      sum+=3;
    if(games[i][0]==games[i][2])
      sum+=1;
  }
  return sum;
}