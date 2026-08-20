open Query.ExtractQuery

let string_of_player = function
  | White -> "white"
  | Black -> "black"

let string_of_piece = function
  | King -> "king"
  | Queen -> "queen"
  | Rook -> "rook"
  | Bishop -> "bishop"
  | Knight -> "knight"

let file_of_char = function
  | 'a' -> file_a
  | 'b' -> file_b
  | 'c' -> file_c
  | 'd' -> file_d
  | 'e' -> file_e
  | 'f' -> file_f
  | 'g' -> file_g
  | 'h' -> file_h
  | _ -> invalid_arg "file_of_char"

let string_of_file f =
  match f with
  | f when f = file_a -> "a"
  | f when f = file_b -> "b"
  | f when f = file_c -> "c"
  | f when f = file_d -> "d"
  | f when f = file_e -> "e"
  | f when f = file_f -> "f"
  | f when f = file_g -> "g"
  | f when f = file_h -> "h"
  | _ -> invalid_arg "char_of_file"

let string_of_rank r =
  match r with
  | r when r = rank_1 -> "1"
  | r when r = rank_2 -> "2"
  | r when r = rank_3 -> "3"
  | r when r = rank_4 -> "4"
  | r when r = rank_5 -> "5"
  | r when r = rank_6 -> "6"
  | r when r = rank_7 -> "7"
  | r when r = rank_8 -> "8"
  | _ -> invalid_arg "char_of_rank"

let rank_of_char = function
  | '1' -> rank_1
  | '2' -> rank_2
  | '3' -> rank_3
  | '4' -> rank_4
  | '5' -> rank_5
  | '6' -> rank_6
  | '7' -> rank_7
  | '8' -> rank_8
  | _ -> invalid_arg "rank_of_char"

let string_of_pos (f,r) =
  string_of_file f ^ string_of_rank r

let pos_of_string s =
  if String.length s <> 2 then
    invalid_arg "square_of_string";
  let file = file_of_char s.[0] in
  let rank = rank_of_char s.[1] in
  (file, rank)
