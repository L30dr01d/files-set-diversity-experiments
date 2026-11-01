module TotalPoints where

points :: [String] -> Int
points = sum . map match
  where
    match [x,':',y]
      | x > y  = 3
      | x < y  = 0
      | x == y = 1