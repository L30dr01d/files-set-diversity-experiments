points = (games) ->
  finalResult = 0
  
  for game in games
    [x, y] = game.split ':'
    if +x > +y
      finalResult += 3
    else if +x == +y
      finalResult += 1
      
  finalResult