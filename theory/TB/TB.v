Require Import TBGen.StratSymTB.TB.
Require Import TBGen.StratSymTB.OCamlTB.

Require Import Chess.Chess.Chess.
Require Import Chess.Util.UIP.
Require Import Games.Util.Dec.
Require Import Chess.TB.Material.
Require Import Chess.TB.Symmetry.

Global Instance Hash_ChessState : IntHash.CondIntHash KRvK.
Proof.
Admitted.

Global Instance ReverseChess : Reversible ChessGame.
Proof.
Admitted.

Global Instance NiceChess : NiceGame ChessGame.
Proof.
  constructor.
  intros s pl pf.
  simpl in pf.
  unfold atomic_chess_res in pf.
  destruct (enum_chess_moves s) eqn:Hs.
  - destruct dec.
    + inversion pf.
      rewrite Player.opp_invol.
      reflexivity.
    + inversion pf.
  - discriminate.
Qed.

(*
Global Instance SymChess : Symmetry ChessGame.
Proof.
  exact SymChess.
Admitted.
*)

Global Instance DiscPiece : Discrete Piece.
Proof.
  constructor.
  intros [] [];
  try (right; discriminate);
  left; reflexivity.
Defined.

Global Instance DiscFile : Discrete File.
Proof.
  apply Fin.Fin_Discrete.
Defined.

Global Instance DiscRank : Discrete Rank.
Proof.
  apply Fin.Fin_Discrete.
Defined.

Global Instance DiscPreMove :
  Discrete PreMove.
Proof.
  constructor.
  intros [p o d] [p' o' d'].
  destruct (eq_dec p p'); [|right; congruence].
  destruct (eq_dec o o'); [|right; congruence].
  destruct (eq_dec d d'); [|right; congruence].
  left; congruence.
Defined.

Global Instance DiscRegMove : forall s,
  Discrete (RegularMove s).
Proof.
  intro s.
  constructor.
  intros m m'.
  destruct (eq_dec (premove m) (premove m')).
  - left; now apply RegularMove_ext.
  - right; congruence.
Defined.

Global Instance DiscChessMove : forall s,
  Games.Util.Dec.Discrete (ChessMove s).
Proof.
  intro s.
  constructor.
  intros [rm] [rm'].
  destruct (eq_dec rm rm').
  - left; congruence.
  - right; congruence.
Defined.

Global Instance KRvK_Fin : FinPred KRvK.
Proof.
Admitted.

Global Instance KRvK_closed : Closed.Closed KRvK.
Proof.
  constructor.
  intros s pf m.
  unfold KRvK.
  apply TotalMaterial_le_trans with (t2 := get_material s).
  - apply TotalMaterial_le_exec_move.
  - exact pf.
Qed.

Global Instance KRvK_dec1 : Closed.Dec1 KRvK.
Proof.
  constructor.
  intro s.
  apply TotalMaterial_le_dec.
Defined.

Global Instance KRvK_bisim_closed :
  Closed.Bisim_closed auto KRvK.
Proof.
  simpl; constructor.
  intros s s' mat [x Hx]; subst.
  unfold KRvK.
  rewrite get_material_act; auto.
Qed.

Definition certified_Chess_TB : OCamlTablebase ChessGame :=
  certified_TB.

(*
Print Assumptions certified_Chess_TB.
*)
