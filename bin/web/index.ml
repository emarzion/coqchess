open Js_of_ocaml
open Query.ExtractQuery
open Query.Read_file

(* ---- Helpers ---- *)

let create_element tag = Dom_html.document##createElement (Js.string tag)
let append_child parent child = Dom.appendChild parent child
let set_style el key value = el##.style##setProperty (Js.string key) (Js.string value) Js.undefined

(* ---- Board ---- *)

let _default_fen = "7k/8/8/8/8/8/8/R6K w - - 0 1"
let _invalid_fen = "k7/8/8/8/8/8/8/R6K w - - 0 1"

let _stalemate_fen = "7k/6R1/7K/8/8/8/8/8 b - - 0 1"

let _kings_fen = "5k2/8/8/8/8/8/8/1K6 w - - 0 1"
let longest_fen = "8/8/8/8/8/8/2Rk4/1K6 b - - 0 1"

let after_move =
  Js.wrap_callback
    (fun orig dest metadata ->
      Firebug.console##log (Js.string "Move detected!");
      Firebug.console##log orig;
      Firebug.console##log dest;
      Firebug.console##log metadata)

let fen_turn fen =
  match String.split_on_char ' ' fen with
  | _board :: turn :: _ ->
      if turn = "w" then "white"
      else if turn = "b" then "black"
      else failwith "Invalid FEN turn"
  | _ ->
      failwith "Invalid FEN"

let make_config fen =
  let events =
    Js.Unsafe.obj [|
      ("after", Js.Unsafe.inject after_move)
    |]
  in

  let movable =
    Js.Unsafe.obj [|
      ("events", Js.Unsafe.inject events)
    |]
  in

  Js.Unsafe.obj [|
    ("fen", Js.Unsafe.inject (Js.string fen));
    ("turnColor", Js.Unsafe.inject (Js.string (fen_turn fen)));
    ("movable", Js.Unsafe.inject movable);
  |]

let log x = Firebug.console##log x

let create_board () =
  let container = create_element "div" in
  container##.id := Js.string "board-container";
  let _ = set_style container "width" "440px" in
  let _ = set_style container "height" "440px" in
  append_child Dom_html.document##.body container;

  let cfg = make_config longest_fen in
  let board = Js.Unsafe.global##Chessground container cfg in

  log (Js.string "=== CHESSGROUND STATE ===");
  log board##.state;

  Js.Unsafe.global##.ChessboardInstance := board;
  board

(* ---- Compatibility Layer --- *)

let player_of_string = function
  | "white" -> White
  | "black" -> Black
  | _ -> failwith "unknown player"

let piece_of_string = function
  | "king" -> King
  | "queen" -> Queen
  | "rook" -> Rook
  | "bishop" -> Bishop
  | "knight" -> Knight
  | _ -> failwith "unknown piece"

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

let pos_of_string s =
  if String.length s <> 2 then
    invalid_arg "square_of_string";
  let file = file_of_char s.[0] in
  let rank = rank_of_char s.[1] in
  (file, rank)

(* ---- Main ---- *)

let convert_to_pair js_arr =
  let ocaml_arr = Js.to_array js_arr in
  let sq : string = Obj.magic (ocaml_arr.(0)) in
  let a = ocaml_arr.(1) in
  let pc : string = a##.role in
  let pl : string = a##.color in
  ((player_of_string pl, piece_of_string pc), pos_of_string sq)

let get_bindings () =
  let board = Js.Unsafe.global##.ChessboardInstance in
  let map = board##.state##.pieces in
  let js_arr = Js.Unsafe.fun_call
    (Js.Unsafe.js_expr "Array.from")
    [| Js.Unsafe.inject map |] in
  let ocaml_arr = Js.to_array js_arr in
  let l = Array.to_list ocaml_arr in
  List.map convert_to_pair l

let get_turn () =
  let board = Js.Unsafe.global##.ChessboardInstance in
  let pl : string = board##.state##.turnColor in
  log "PLAYER";
  log pl;
  player_of_string pl

let log_player player =
  match player with
  | White -> log "white"
  | Black -> log "black"

let () =
  let _board = create_board () in
  let tb = make_tb in
  let bindings = get_bindings () in
  let pl = get_turn () in
  match mk_KRvK_bound pl bindings with
  | Success s ->
      log "success!";
      begin match query tb s with
      | Some (pl,n) ->
          log "win!";
          log_player pl;
          log n
      | None -> log "draw!"
      end
  | Error msg ->
      log "failure!";
      log msg


(*
python3 -m http.server 8000
*)

(*
  let _st = js_iterator_to_list board##.state##.pieces##entries in
*)
