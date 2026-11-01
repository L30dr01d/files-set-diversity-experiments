int points( const char* const games[10] )
{
    int total = 0;
  
    for ( int i = 0; i < 10; i++ )
    {
        int x = games[i][0] - '0';
        int y = games[i][2] - '0';
      
        if ( x == y )
        {
            total += 1;
        }
        else if ( x > y )
        {
            total += 3;
        }
    }
  
    return total;
}
