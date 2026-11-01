package kata

import ( "strings" )

func Points(games []string) int {
  result := 0
  for _, game := range games {
    str := strings.Split(game, ":")
    x, y := str[0], str[1]
    switch {
      case x > y:
        result += 3
      case x == y:
        result += 1
    }
  }
  return result
}