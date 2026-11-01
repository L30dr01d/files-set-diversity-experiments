USING: combinators kernel math.order math.parser sequences ;
IN: kata

: parse ( str -- m n ) [ first digit> ] [ last digit> ] bi ;

: score ( m n -- score )
    <=> {
        { +gt+ [ 3 ] }
        { +lt+ [ 0 ] }
        [ drop 1 ]
    } case ;

: points ( seq -- n ) [ parse score ] map-sum ;