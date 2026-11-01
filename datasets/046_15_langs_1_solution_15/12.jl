function points(games)
  sum(re[1]>re[3] ? 3 : re[1]==re[3] ? 1 : 0 for re in games)
end