module Kata

let getScore (text: string): int = 
    match compare text[0] text[2] with
    | 1 -> 3
    | 0 -> 1
    | _ -> 0

let points (games: list<string>) : int = List.map (fun x -> getScore x) games |> List.sum