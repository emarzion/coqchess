open Js_of_ocaml
open Query.ExtractQuery

open Compat
open Util
open Model

let palette_pieces = [
  (King, White);
  (King, Black);
  (Rook, White);
]

type ui_state = {
  board : Js.Unsafe.any;
  toggle : Dom_html.buttonElement Js.t;
  blank : Dom_html.buttonElement Js.t;
  play_as_white : Dom_html.buttonElement Js.t;
  play_as_black : Dom_html.buttonElement Js.t;
  turn_indicator : Dom_html.divElement Js.t;
  game_value : Dom_html.divElement Js.t;
  edit_tab : Dom_html.divElement Js.t;
  query_tab : Dom_html.divElement Js.t;
  play_tab : Dom_html.divElement Js.t;
  move_list : Dom_html.divElement Js.t;
  palette_wrap : Dom_html.divElement Js.t;
  palette : (piece * player * Dom_html.divElement Js.t) list;
  last_drag : (piece * player) option ref;
}

let legal_dests moves =
  let grouped =
    List.fold_left
      (fun acc move ->
        let orig = string_of_pos move.origin in
        let dest = string_of_pos move.dest in

        let old =
          match List.assoc_opt orig acc with
          | Some xs -> xs
          | None -> []
        in

        (orig, dest :: old) ::
        List.remove_assoc orig acc)
      []
      moves
  in

  let map =
    Js.Unsafe.new_obj (Js.Unsafe.pure_js_expr "Map") [||]
  in

  List.iter
    (fun (orig, dests) ->
      let js_dests =
        Js.array
          (Array.of_list
             (List.map (fun s -> Js.string s) dests))
      in

      ignore (Js.Unsafe.meth_call map "set"
        [|
          Js.Unsafe.inject (Js.string orig);
          Js.Unsafe.inject js_dests;
        |]))
    grouped;
  map

let mk_field k v =
  (k, Js.Unsafe.inject (Js.string v))

let piece_obj pc pl =
  Js.Unsafe.obj [|
    mk_field "role" (string_of_piece pc);
    mk_field "color" (string_of_player pl);
  |]

let pieces_obj pieces =
  let map = Js.Unsafe.new_obj (Js.Unsafe.pure_js_expr "Map") [||] in
  List.iter
    (fun ((pos, pc), pl) ->
      ignore (Js.Unsafe.meth_call map "set"
        [|
          Js.Unsafe.inject (Js.string (string_of_pos pos));
          Js.Unsafe.inject (piece_obj pc pl);
        |]))
    pieces;
  map

let render_pieces ui pieces =
  let cfg =
    Js.Unsafe.obj [|
      ("pieces", Js.Unsafe.inject pieces);
    |]
  in

  ignore (
    Js.Unsafe.meth_call ui.board "set"
      [| Js.Unsafe.inject cfg |]
  )

let movable_config state =
  match !state with
  | Model.Edit _ ->
      Js.Unsafe.obj [|
        ("free", Js.Unsafe.inject Js._true);
      |]

  | Model.Query st ->
      let moves =
        enum_chess_moves st in
      let dests = legal_dests moves in

      Js.Unsafe.obj [|
        ("free", Js.Unsafe.inject Js._false);
        ("dests", Js.Unsafe.inject dests);
      |]
  | Model.SelectingPlayer _ ->
      Js.Unsafe.obj [| |]
  | Model.Play (st,_) ->
      let moves =
        enum_chess_moves st in
      let dests = legal_dests moves in
      Js.Unsafe.obj [|
        ("free", Js.Unsafe.inject Js._false);
        ("dests", Js.Unsafe.inject dests);
      |]


let render_movable state ui =
  let movable =
    movable_config state
  in

  let cfg =
    Js.Unsafe.obj [|
      ("movable", Js.Unsafe.inject movable);
    |]
  in

  ignore (Js.Unsafe.meth_call ui.board "set"
    [| Js.Unsafe.inject cfg |])

let board_size = 440
let gap = 70                    (* board → turn indicator → move list space *)
let move_list_width = 250       (* change this one value to resize the right column *)
let wrapper_width = board_size + gap + move_list_width   (* 440 + 70 + 250 = 760 *)

let board_size = 440
let gap = 70
let move_list_width = 250
let _wrapper_width = board_size + gap + move_list_width
let square_size = board_size / 8

let render_toggle state ui =
  ui.toggle##.textContent := Js.some (Js.string "toggle player");

  match !state with
  | Model.Edit _ ->
      set_style ui.toggle "display" "block";
      set_style ui.palette_wrap "width" (string_of_int (square_size * List.length palette_pieces) ^ "px");
      set_style ui.palette_wrap "overflow" "visible";
      List.iter (fun (_,_,elt) ->
        set_style elt "display" "block") ui.palette
  | _ ->
      set_style ui.palette_wrap "width" "0px";
      set_style ui.palette_wrap "overflow" "hidden";
      set_style ui.toggle "display" "none";
      List.iter (fun (_,_,elt) ->
        set_style elt "display" "none") ui.palette

let render_blank state ui =
  ui.blank##.textContent := Js.some (Js.string "clear board");

  match !state with
  | Model.Edit _ ->
      set_style ui.blank "display" "block";
      List.iter (fun (_,_,elt) ->
        set_style elt "display" "block") ui.palette
  | _ ->
      set_style ui.blank "display" "none";
      List.iter (fun (_,_,elt) ->
        set_style elt "display" "none") ui.palette

let render_play_as_white state ui =
  ui.play_as_white##.textContent := Js.some (Js.string "play as white");

  match !state with
  | Model.SelectingPlayer _ ->
      set_style ui.play_as_white "display" "block";
  | _ ->
      set_style ui.play_as_white "display" "none"

let render_play_as_black state ui =
  ui.play_as_black##.textContent := Js.some (Js.string "play as black");

  match !state with
  | Model.SelectingPlayer _ ->
      set_style ui.play_as_black "display" "block";
  | _ ->
      set_style ui.play_as_black "display" "none"

let render_turn_indicator state ui =
  let curr =
    match !state with
    | Model.Edit s -> s.es_board.edit_to_play
    | Model.Query st -> st.chess_to_play
    | Model.SelectingPlayer st -> st.chess_to_play
    | Model.Play(st,_) -> st.chess_to_play
  in

  set_style ui.turn_indicator
    "background-color"
    (string_of_player curr);

  match curr with
  | White ->
      set_style ui.turn_indicator "bottom" "0px";
      set_style ui.turn_indicator "top" "auto"
  | Black ->
      set_style ui.turn_indicator "top" "0px";
      set_style ui.turn_indicator "bottom" "auto"

let gv_text o =
  match o with
  | Some (pl,n) -> string_of_player pl ^ " wins in " ^ string_of_int n
  | None -> "draw"

let gray = "#aaa"
let black = "#000"
let white = "#fff"

type colors = {
  background : string;
  text : string
}

let white_colors = {
  background = white;
  text = black;
}

let black_colors = {
  background = black;
  text = white;
}

let draw_colors = {
  background = gray;
  text = black
}

let get_colors o =
  match o with
  | Some (White, _) -> white_colors
  | Some (Black, _) -> black_colors
  | None -> draw_colors

let render_game_value tb state ui =
  match !state with
  | Model.Edit s ->
    ui.game_value##.textContent :=
      begin match s.es_invalid with
      | true -> Js.some (Js.string "invalid KRvK position")
      | false -> Js.null
      end;
    set_style ui.game_value "background-color" white;
    set_style ui.game_value "color" black;
  | Model.Query s ->
    let res = query tb s in
    let colors = get_colors res in
    set_style ui.game_value "background-color" colors.background;
    set_style ui.game_value "color" colors.text;
    ui.game_value##.textContent := Js.some (Js.string (gv_text res))
  | Model.Play (_,str) ->
      begin match Lazy.force str with
      | Atom_strategy(_,res) ->
        let txt =
        begin match res with
        | Win pl -> "Game over: " ^ string_of_player pl ^ " wins"
        | Draw -> "Game over: stalemate"
        end in
        set_style ui.game_value "background-color" white;
        set_style ui.game_value "color" black;
        ui.game_value##.textContent := Js.some (Js.string txt);
      | _ ->
        ui.game_value##.textContent := Js.null;
        set_style ui.game_value "background-color" white;
        set_style ui.game_value "color" black
      end
  | _ ->
    ui.game_value##.textContent := Js.null;
    set_style ui.game_value "background-color" white;
    set_style ui.game_value "color" black

let select tab =
  set_style tab "font-weight" "bold";
  set_style tab "border-bottom" "2px solid black"

let deselect tab =
  set_style tab "font-weight" "normal";
  set_style tab "border-bottom" "none"

let render_tabs state ui =
  set_style ui.edit_tab "padding" "5px 2px";
  set_style ui.query_tab "padding" "5px 2px";
  set_style ui.play_tab "padding" "5px 2px";

  match !state with
  | Model.Edit _ ->
      select ui.edit_tab;
      deselect ui.query_tab;
      deselect ui.play_tab
  | Model.Query _ ->
      deselect ui.edit_tab;
      select ui.query_tab;
      deselect ui.play_tab
  | Model.SelectingPlayer _ ->
      deselect ui.edit_tab;
      deselect ui.query_tab;
      select ui.play_tab
  | Model.Play _ ->
      deselect ui.edit_tab;
      deselect ui.query_tab;
      select ui.play_tab

let alg_of_piece (p : piece) : string =
  match p with
  | King -> "K"
  | Queen -> "Q"
  | Rook -> "R"
  | Bishop -> "B"
  | Knight -> "N"

let alg_of_move (m : chessMove) : string =
  alg_of_piece (m.piece0) ^ string_of_pos (m.origin) ^ string_of_pos (m.dest)

let move_text (m,res) =
  alg_of_move m ^ ": " ^ gv_text res

let moves_sorted tb s =
  let moves = enum_chess_moves s in
  let move_pairs = List.map (fun m ->
    let s' = exec_ChessMove s m in
    (m, query tb s')) moves in
  List.sort (fun (_,o1) (_,o2) ->
    if p_leb s.chess_to_play o1 o2 then 1 else -1
    ) move_pairs

let rec render tb state ui =

  let tups =
    match !state with
    | Model.Edit s -> dump_board s.es_board.edit_board
    | Model.Query st -> dump_board st.board0
    | Model.SelectingPlayer st -> dump_board st.board0
    | Model.Play (st,_) -> dump_board st.board0
  in

  let pieces = pieces_obj tups in
  render_game_value tb state ui;
  render_movable state ui;
  render_toggle state ui;
  render_blank state ui;
  render_play_as_white state ui;
  render_play_as_black state ui;
  render_pieces ui pieces;
  render_turn_indicator state ui;
  render_tabs state ui;

  begin match !state with
  | Model.Play (st,str) ->
    begin match Lazy.force str with
    | Eloise_strategy (_,mv,str') ->
      state := Model.Play (exec_ChessMove st (Obj.magic mv), str');
      render tb state ui
    | _ -> ()
    end
  | _ -> ()
  end;
  
  match !state with
  | Model.Edit _ ->
      ui.move_list##.innerHTML := Js.string ""
  | Model.Query st ->
      let move_vals = moves_sorted tb st in
      render_moves tb state ui move_vals
  | _ -> 
      ui.move_list##.innerHTML := Js.string ""
      (* TODO? *) 

and render_moves tb state ui move_vals =
  ui.move_list##.innerHTML := Js.string "";

  List.iter
    (fun move_val ->
      let button = Dom_html.createButton Dom_html.document in

      button##.textContent :=
        Js.some (Js.string (move_text move_val));

      let colors = get_colors (snd move_val) in
      set_style button "background-color" colors.background;
      set_style button "color" colors.text;
      set_style button "display" "block";
      set_style button "border" "none";
      set_style button "padding" "2px 0px";
      set_style button "cursor" "pointer";
      set_style button "font-size" "16px";
      set_style button "min-width" "180px";
      set_style button "text-align" "left";

      append_child ui.move_list button;

      ignore (
        Dom_html.addEventListener button
          Dom_html.Event.click
          (Dom_html.handler (fun _ ->
            state := Action.apply tb (Action.SelectMove (fst move_val)) !state;
            render tb state ui;
            Js._false))
          Js._false
      ))
    move_vals

let init_config =
  let empty_pieces =
    Js.Unsafe.new_obj (Js.Unsafe.pure_js_expr "Map") [||]
  in

  Js.Unsafe.obj [|
    ("pieces", Js.Unsafe.inject empty_pieces);
  |]

let class_name pc pl =
  "piece " ^ string_of_player pl ^ " " ^ string_of_piece pc

let palette_piece pc pl =
  let elt = create_element "piece" in
  elt##.className := Js.string (class_name pc pl);
  set_style elt "pointer-events" "auto";
  set_style elt "position" "relative";
  set_style elt "display" "inline-block";
  set_style elt "width" (string_of_int square_size ^ "px");
  set_style elt "height" (string_of_int square_size ^ "px");
  set_style elt "flex-shrink" "0";
  elt

let init_ui () =
  let wrapper = create_element "div" in
  set_style wrapper "display" "flex";
  set_style wrapper "flex-direction" "column";
  set_style wrapper "gap" "10px";
  set_style wrapper "width" (string_of_int wrapper_width ^ "px");
  set_style wrapper "font-family" "sans-serif";

  (* ---- Top row ---- *)
  let top_row = create_element "div" in
  set_style top_row "display" "flex";
  set_style top_row "gap" (string_of_int gap ^ "px");
  set_style top_row "width" "100%";

  let tabs = create_element "div" in
  set_style tabs "display" "flex";
  set_style tabs "gap" "20px";
  set_style tabs "width" (string_of_int board_size ^ "px");
  set_style tabs "flex-shrink" "0";

  let edit_tab = create_element "div" in
  edit_tab##.textContent := Js.some (Js.string "Edit");
  set_style edit_tab "cursor" "pointer";
  set_style edit_tab "font-weight" "bold";

  let query_tab = create_element "div" in
  query_tab##.textContent := Js.some (Js.string "Query");
  set_style query_tab "cursor" "pointer";

  let play_tab = create_element "div" in
  play_tab##.textContent := Js.some (Js.string "Play");
  set_style play_tab "cursor" "pointer";

  append_child tabs edit_tab;
  append_child tabs query_tab;
  append_child tabs play_tab;

  let game_value = create_element "div" in
  set_style game_value "width" (string_of_int move_list_width ^ "px");
  set_style game_value "flex-shrink" "0";
  set_style game_value "font-size" "18px";
  set_style game_value "display" "flex";
  set_style game_value "align-items" "center";
  set_style game_value "border" "1px solid black";
  set_style game_value "padding" "2px 8px";
  set_style game_value "box-sizing" "border-box";

  append_child top_row tabs;
  append_child top_row game_value;

  (* ---- Bottom row ---- *)
  let bottom_row = create_element "div" in
  set_style bottom_row "display" "flex";
  set_style bottom_row "gap" (string_of_int gap ^ "px");
  set_style bottom_row "width" "100%";

  (* --- NEW: board wrapper (relative, holds board + indicator) --- *)
  let board_wrapper = create_element "div" in
  set_style board_wrapper "position" "relative";
  set_style board_wrapper "width" (string_of_int board_size ^ "px");
  set_style board_wrapper "height" (string_of_int board_size ^ "px");
  set_style board_wrapper "flex-shrink" "0";

  (* Board container – Chessground will render inside this *)
  let container = create_element "div" in
  container##.id := Js.string "board-container";
  set_style container "width" "100%";
  set_style container "height" "100%";
  (* No position: relative needed here – board_wrapper handles it *)

  (* Turn indicator – now a sibling of container, inside board_wrapper *)
  let turn_indicator = create_element "div" in
  set_style turn_indicator "width" "40px";
  set_style turn_indicator "height" "40px";
  set_style turn_indicator "position" "absolute";
  set_style turn_indicator "left" "100%";           (* exactly at board's right edge *)
  set_style turn_indicator "margin-left" "15px";    (* centre in the 70px gap *)
  set_style turn_indicator "top" "0px";
  set_style turn_indicator "border" ("1px solid " ^ black);
  set_style turn_indicator "background" "white";
  set_style turn_indicator "z-index" "2";

  (* Assemble board_wrapper *)
  append_child board_wrapper container;
  append_child board_wrapper turn_indicator;  (* indicator is now outside Chessground's realm *)

  (* Move list *)
  let move_list = create_element "div" in
  set_style move_list "width" (string_of_int move_list_width ^ "px");
  set_style move_list "height" (string_of_int board_size ^ "px");
  set_style move_list "overflow-y" "scroll";
  set_style move_list "border" "1px solid #000";
  set_style move_list "box-sizing" "border-box";
  set_style move_list "flex-shrink" "0";
  set_style move_list "padding" "8px 12px";

  append_child bottom_row board_wrapper;   (* now append the wrapper, not container *)
  append_child bottom_row move_list;

  (* ---- Assemble main wrapper ---- *)
  append_child wrapper top_row;
  append_child wrapper bottom_row;

  append_child Dom_html.document##.body wrapper;

  let palette_wrap = create_element "div" in
  palette_wrap##.className := Js.string "cg-wrap";   (* match the selector *)
  set_style palette_wrap "width" (string_of_int (square_size * List.length palette_pieces) ^ "px");
  set_style palette_wrap "height" (string_of_int square_size ^ "px");
  set_style palette_wrap "position" "relative";
  set_style palette_wrap "z-index" "1000";
  set_style palette_wrap "display" "flex";
  set_style palette_wrap "flex-direction" "row";

  let palette = List.map (fun (pc,pl) ->
    (pc, pl, palette_piece pc pl)) palette_pieces in

  List.iter (fun (_,_,elt) -> append_child palette_wrap elt) palette;
  append_child Dom_html.document##.body palette_wrap;

  let toggle = Dom_html.createButton Dom_html.document in
  set_style toggle "padding" "8px 16px";
  set_style toggle "font-size" "16px";
  set_style toggle "margin-top" "5px";

  let blank = Dom_html.createButton Dom_html.document in
  set_style blank "padding" "8px 16px";
  set_style blank "font-size" "16px";
  set_style blank "margin-top" "5px";

  let play_as_white = Dom_html.createButton Dom_html.document in
  set_style play_as_white "padding" "8px 16px";
  set_style play_as_white "font-size" "16px";
  set_style play_as_white "margin-top" "5px";

  let play_as_black = Dom_html.createButton Dom_html.document in
  set_style play_as_black "padding" "8px 16px";
  set_style play_as_black "font-size" "16px";
  set_style play_as_black "margin-top" "5px";

  let left_controls = create_element "div" in
  set_style left_controls "width"
    (string_of_int (square_size * List.length palette_pieces) ^ "px");
  set_style left_controls "height" (string_of_int square_size ^ "px");
  set_style left_controls "display" "flex";
  set_style left_controls "align-items" "center";

  let controls = create_element "div" in
  set_style controls "display" "flex";
  set_style controls "align-items" "center";
  set_style controls "gap" "8px";

(*
  let controls2 = create_element "div" in
  set_style controls2 "display" "flex";
  set_style controls2 "align-items" "center";
  set_style controls2 "gap" "8px";
*)

  append_child controls palette_wrap;
  append_child controls toggle;
  append_child controls blank;
  append_child controls play_as_white; (* *)
  append_child controls play_as_black; (* *)

  append_child Dom_html.document##.body controls;
(**  append_child Dom_html.document##.body controls2; *)

  (* ---- Initialise Chessground (now it only touches container) ---- *)
  let board = Js.Unsafe.global##Chessground container init_config in

  { board; toggle; blank; play_as_white; play_as_black;
    turn_indicator; game_value; edit_tab; query_tab; play_tab;
    move_list; palette; palette_wrap; last_drag = ref None;
  }

let drag_piece tb state ui =
  Js.wrap_callback
    (fun orig dest _ ->
      let em = {
        orig = pos_of_string orig;
        dest0 = pos_of_string dest } in
      state := Action.apply tb (Action.DragPiece em) !state;
      render tb state ui
    )

let new_piece tb state ui =
  Js.wrap_callback
    (fun _role dest _ ->
      let pos = pos_of_string dest in
      begin match !(ui.last_drag) with
      | Some (pc, pl) ->
          state := Action.apply tb
            (Action.AddPiece (pc, pl, pos))
            !state
      | None -> ()
      end;
      ui.last_drag := None;
      render tb state ui)

let toggle_player tb state ui =
  ignore (
    Dom_html.addEventListener ui.toggle
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb Action.TogglePlayer !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let blank_board tb state ui =
  ignore (
    Dom_html.addEventListener ui.blank
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb Action.BlankBoard !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let select_white tb state ui =
  ignore (
    Dom_html.addEventListener ui.play_as_white
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb (Action.SelectPlayer White) !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let select_black tb state ui =
  ignore (
    Dom_html.addEventListener ui.play_as_black
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb (Action.SelectPlayer Black) !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let drag_new_piece ui (pc, pl, elt) =
  ignore (
    Dom_html.addEventListener elt
      Dom_html.Event.mousedown
      (Dom_html.handler (fun ev ->
        ui.last_drag := Some (pc, pl);
        ignore (
          Js.Unsafe.meth_call ui.board "dragNewPiece"
            [|
              Js.Unsafe.inject (piece_obj pc pl);
              Js.Unsafe.inject ev;
              Js.Unsafe.inject Js._true;
            |]
        );

        Js._false))
      Js._false
  )

let drag_new_pieces ui =
  List.iter (drag_new_piece ui) ui.palette

let edit_mode tb state ui =
  ignore (
    Dom_html.addEventListener ui.edit_tab
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb Action.EditMode !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let query_mode tb state ui =
  ignore (
    Dom_html.addEventListener ui.query_tab
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb Action.QueryMode !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let play_mode tb state ui =
  ignore (
    Dom_html.addEventListener ui.play_tab
      Dom_html.Event.click
      (Dom_html.handler (fun _ ->
      state := Action.apply tb Action.PlayMode !state;
      render tb state ui;
      Js._false))
      Js._false;
  )

let add_functionality tb state ui =
  let events =
    Js.Unsafe.obj [|
      ("after", Js.Unsafe.inject (drag_piece tb state ui));
      ("afterNewPiece", Js.Unsafe.inject (new_piece tb state ui));   
    |]
  in

  let cfg =
    Js.Unsafe.obj [|
      ("movable", Js.Unsafe.inject (Js.Unsafe.obj [|
        ("events", Js.Unsafe.inject events);
      |]));

      ("highlight", Js.Unsafe.inject (Js.Unsafe.obj [|
        ("lastMove", Js.Unsafe.inject Js._false);
      |]));
    |]
  in

  toggle_player tb state ui;
  blank_board tb state ui;
  select_white tb state ui;
  select_black tb state ui;
  edit_mode tb state ui;
  query_mode tb state ui;
  play_mode tb state ui;
  drag_new_pieces ui;

  ignore (Js.Unsafe.meth_call ui.board "set"
    [| Js.Unsafe.inject cfg |])

let init tb state =
  let ui = init_ui () in
  Js.Unsafe.global##.ChessboardInstance := ui.board;
  add_functionality tb state ui;
  render tb state ui
