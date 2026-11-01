       identification division.
       program-id. Points.
       data division.
       local-storage section.
       01 p pic 9(1).
       01 v pic 9(1).
       linkage section.
       01  games.
           03 game pic x(3) occurs 10 times
                            INDEXED BY I.
       01  result  pic 9(2).
      
       procedure division using games result.
       initialize result
       PERFORM VARYING I FROM 1 BY 1 UNTIL I = 11
          UNSTRING GAME(I) DELIMITED BY ':' INTO P V
          EVALUATE TRUE
          WHEN P > V ADD 3 TO RESULT
          WHEN P = V ADD 1 TO RESULT.
       end program Points.