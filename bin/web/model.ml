open Query.ExtractQuery

module Model = struct

  type editState = {
    es_board : editBoard;
    es_invalid : bool
  }

  type t =
    | Edit of editState
    | Query of chessState
    | SelectingPlayer of chessState
    | Play of chessState * strategy

  let init_editState = {
    es_board = init_edit;
    es_invalid = false;
  }

  let init : t =
    Edit init_editState

end

(* Action *)

let user_step st str (mv : chessMove) =
  match Lazy.force str with
  | Abelard_strategy (_, strs) ->
      (exec_ChessMove st (Obj.magic mv), strs (Obj.magic mv))
  | Atom_strategy _ ->
      failwith "Atom_strategy called unexpectedly"
  | Eloise_strategy (_,_,_) ->
      failwith "Eloise_strategy called unexpectedly"

module Action = struct

  type t =
  | DragPiece of editMove
  | TogglePlayer
  | EditMode
  | QueryMode
  | PlayMode
  | SelectPlayer of player
  | SelectMove of chessMove
  | AddPiece of piece * player * pos
  | BlankBoard

  let apply tb (a : t) (s : Model.t) : Model.t =
    match s with
    | Edit e ->
      begin match a with
      | DragPiece em -> Edit { e with es_board = execEditMove em e.es_board }
      | TogglePlayer -> Edit { e with es_board = toggle_player e.es_board }
      | EditMode -> Edit e
      | QueryMode ->
        begin match mk_KRvK_bound e.es_board with
        | Success st -> Query st
        | Error _msg -> Edit { e with es_invalid = true }
        end
      | PlayMode ->
        begin match mk_KRvK_bound e.es_board with
        | Success st -> SelectingPlayer st
        | Error _msg -> Edit { e with es_invalid = true }
        end
      | SelectPlayer _ -> Edit e
      | SelectMove _ -> Edit e
      | AddPiece(pc, pl, pos) ->
          Model.Edit { e with es_board =
            { e.es_board with edit_board = place_piece pl pc pos e.es_board.edit_board }
          }
      | BlankBoard -> Edit {
          es_board = { e.es_board with edit_board = blank_board };
          es_invalid = false }
      end
    | Query st ->
      begin match a with
      | DragPiece em ->
        begin match lookup_piece em.orig st.board0 with
        | Some (_,pc) ->
          let m = { piece0 = pc; origin = em.orig; dest = em.dest0 } in
          Query (exec_ChessMove st m)
        | None -> s
        end
      | TogglePlayer -> s
      | EditMode -> Edit {
          es_board =
            editBoard_of_PreChessState (preChessState_of_ChessState st);
          es_invalid = false;
        }
      | QueryMode -> Query st
      | PlayMode -> SelectingPlayer st
      | SelectPlayer _ -> Query st
      | SelectMove m -> Query (exec_ChessMove st m)
      | AddPiece(_,_,_) -> s
      | BlankBoard -> s
      end
    | SelectingPlayer st ->
      begin match a with
      | DragPiece _ -> SelectingPlayer st
      | TogglePlayer -> SelectingPlayer st
      | EditMode -> Edit {
          es_board =
            editBoard_of_PreChessState (preChessState_of_ChessState st);
          es_invalid = false;
        }
      | QueryMode -> Query st
      | PlayMode -> SelectingPlayer st
      | SelectPlayer pl -> Play (st, tb_strat (opp0 pl) st tb)
      | SelectMove _ -> SelectingPlayer st
      | AddPiece(_,_,_) -> SelectingPlayer st
      | BlankBoard -> SelectingPlayer st
      end
    | Play (st, str) ->
      begin match a with
      | DragPiece em ->
        begin match lookup_piece em.orig st.board0 with
        | Some (_,pc) ->
          let m = { piece0 = pc; origin = em.orig; dest = em.dest0 } in
          let (st', str') = user_step st str m in
          Play (st', str')
        | None -> s
        end
      | TogglePlayer -> Play (st, str)
      | EditMode -> Edit {
          es_board =
            editBoard_of_PreChessState (preChessState_of_ChessState st);
          es_invalid = false;
        }
      | QueryMode -> Query st
      | PlayMode -> Play (st, str)
      | SelectPlayer _ -> Play (st, str)
      | SelectMove _ -> Play (st, str)
      | AddPiece(_,_,_) -> Play (st, str)
      | BlankBoard -> Play (st, str)
      end
end