int points(const char* const games[10])
{
   int points = 0;
   for (int i = 0, sz = 10, x, y; i < sz; i++)
   {
      if (sscanf(games[i], "%d:%d", &x, &y) != 2)
      {
         return -1;
      }
      points += x > y ? 3 : x == y ? 1 : 0;
   }
   return points;
}