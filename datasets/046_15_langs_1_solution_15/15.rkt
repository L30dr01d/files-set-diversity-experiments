#lang racket

(provide points)

(define (points games)
  (for/sum [(g games)]
    (let [(a (string-ref g 0))
          (b (string-ref g 2))]
      (cond
        [(char>? a b) 3]
        [(char=? a b) 1]
        [else 0]))))