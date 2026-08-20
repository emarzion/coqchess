Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Require Import ExtrOCamlInt63.
Require Import Games.Util.Dec.
Require Import Chess.Util.Fin.
Extraction Language OCaml.

Require Import Games.Game.Game.
Require Import Games.Game.Strategy.
Require Import Games.Game.Player.
Require Import Chess.TB.MakeState.
Require Import Chess.Chess.Chess.
Require Import TBGen.StratSymTB.TB.
Require Import TBGen.StratSymTB.OCamlTB.

Require Import List.
Import ListNotations.

Set Warnings "-extraction-default-directory".

Definition query : OCamlTablebase ChessGame ->
  ChessState -> option (Player * nat) :=
  query_TB.

Fixpoint max_by {X} (x_leb : X -> X -> bool) (xs : list X) : option X :=
  match xs with
  | [] => None
  | x :: xs' =>
    match max_by x_leb xs' with
    | None => Some x
    | Some y => if x_leb x y then Some y else Some x
    end
  end.

Lemma max_by_ne_Some {X} x_leb (xs : list X) (pf : xs <> []) :
  { x : X & max_by x_leb xs = Some x }.
Proof.
  destruct xs.
  - elim (pf eq_refl).
  - simpl.
    destruct (max_by x_leb xs).
    + destruct (x_leb x x0).
      * exists x0; reflexivity.
      * exists x; reflexivity.
    + exists x; reflexivity.
Defined.

Definition max_by_ne {X} x_leb (xs : list X) (pf : xs <> []) : X :=
  projT1 (max_by_ne_Some x_leb xs pf).

Lemma move_enum_all_ne {G} {s : Game.GameState G} (s_res : atomic_res s = None) : enum_moves s <> [].
Proof.
  intro pf.
  destruct (nil_atomic_res pf); congruence.
Qed.

Definition p_leb (pl : Player) (r1 r2 : option (Player * nat)) : bool :=
  match pl with
  | White =>
    match r1, r2 with
    | Some (Black, m), Some (Black, n) => Nat.leb m n
    | Some (Black, _), _ => true
    | None, None => true
    | None, Some (White, _) => true
    | Some (White, m), Some (White, n) => Nat.leb n m
    | _, _ => false
    end
  | Black =>
    match r1, r2 with
    | Some (White, m), Some (White, n) => Nat.leb m n
    | Some (White, _), _ => true
    | None, None => true
    | None, Some (Black, _) => true
    | Some (Black, m), Some (Black, n) => Nat.leb n m
    | _, _ => false
    end
  end.

Definition atomic_chess_res_fast
  (s : ChessState) : option Result :=
  let pl := chess_to_play s in
  match enum_chess_moves s with
  | [] =>
    match is_threatened_byb (board s) (king s pl) (opp pl) with
    | true => Some (Win (opp pl))
    | false => Some Draw
    end
  | _ :: _ => None
  end.

Lemma atomic_chess_res_fast_correct s :
  atomic_chess_res_fast s =
  @atomic_res ChessGame s.
Proof.
  simpl.
  unfold atomic_chess_res_fast, atomic_chess_res.
  destruct enum_chess_moves; auto.
  destruct dec as [chk|no_chk]; unfold in_check in *.
  - specialize (chk (king s (chess_to_play s))
      (lookup_king s _)).
    rewrite is_threatened_byb_iff in chk.
    rewrite chk; auto.
  - destruct is_threatened_byb eqn:Hthr; auto.
    rewrite <- is_threatened_byb_iff in Hthr.
    elim no_chk; intros pos Hpos.
    apply s in Hpos; subst; auto.
Qed.

CoFixpoint tb_strat pl (s : ChessState)
  (tb : OCamlTablebase ChessGame) :
  @strategy ChessGame pl s.
Proof.
  - destruct (atomic_chess_res_fast s) eqn:s_res;
    rewrite atomic_chess_res_fast_correct in s_res.
    + eapply atom_strategy; eauto.
    + destruct (player_id_or_opp_r_t (@to_play ChessGame s) pl) as [s_play|s_play].
      * pose (m := max_by_ne
          (fun m1 m2 => p_leb pl
             (query_TB tb (@exec_move ChessGame s m1))
             (query_TB tb (@exec_move ChessGame s m2))
          ) (@enum_moves ChessGame s) (move_enum_all_ne s_res)).
        exact (eloise_strategy s_res s_play m (@tb_strat pl _ tb)).
      * exact (abelard_strategy s_res s_play (fun m =>
          @tb_strat pl _ tb)).
Defined.

Definition dump_board (b : Board) : list (Pos * Piece * Player) :=
  let m := MaterialPositions.mp_of_board b in
  flat_map (fun pc => map (fun pos => (pos, pc, White))
    (m White pc)) all_piece ++
  flat_map (fun pc => map (fun pos => (pos, pc, Black))
    (m Black pc)) all_piece.

Extraction "ExtractQuery.ml"
  p_leb
  tb_strat
  dump_board
  enum_chess_moves
  buildMove
  execEditMove
  toggle_player
  init_edit
  mk_KRvK_bound
  exec_ChessMove
  query
  enum_chess_moves
  OCamlTablebase
  file_a file_b file_c file_d file_e file_f file_g file_h
  rank_1 rank_2 rank_3 rank_4 rank_5 rank_6 rank_7 rank_8.
