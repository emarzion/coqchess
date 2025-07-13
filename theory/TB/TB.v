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
  intros c p.
  apply PeanoNat.Nat.le_trans with (m := count c p (board s)).
  - apply count_exec_move.
  - apply pf.
Qed.

Class ExhaustibleT X : Type := {
  sigT_dec : forall P : X -> Prop,
    (forall x, {P x} + {~ P x}) ->
    { x : X & P x } + ({ x : X & P x} -> Empty_set)
  }.

Lemma pi_dec {X} `{ExhaustibleT X} {P : X -> Prop} :
  (forall x, {P x} + {~ P x}) ->
  {forall x, P x} + { ~ (forall x, P x) }.
Proof.
  intro P_dec.
  destruct (sigT_dec (fun x => ~ P x)).
  - intro x.
    destruct (P_dec x).
    + right; tauto.
    + now left.
  - right; intro pf.
    destruct s as [x px].
    apply px; apply pf.
  - left; intro x.
    destruct (P_dec x); auto.
    elim e.
    exists x; auto.
Defined.

Instance Player_ExhT : ExhaustibleT Player.Player.
Proof.
  constructor.
  intros P P_dec.
  destruct (P_dec Player.Black); [left; eexists; eauto|].
  destruct (P_dec Player.White); [left; eexists; eauto|].
  right; intros [[|] px]; contradiction.
Defined.

Instance Piece_ExhT : ExhaustibleT Piece.
Proof.
  constructor.
  intros P P_dec.
  destruct (P_dec King); [left; eexists; eauto|].
  destruct (P_dec Queen); [left; eexists; eauto|].
  destruct (P_dec Rook); [left; eexists; eauto|].
  destruct (P_dec Bishop); [left; eexists; eauto|].
  destruct (P_dec Knight); [left; eexists; eauto|].
  right; intros [x px]; destruct x; contradiction.
Defined.

Global Instance KRvK_dec1 : Closed.Dec1 KRvK.
Proof.
  constructor.
  intro s.
  unfold KRvK.
  apply pi_dec; intro c.
  apply pi_dec; intro p.
  apply Compare_dec.le_dec.
Defined.

Global Instance KRvK_bisim_closed :
  Closed.Bisim_closed auto KRvK.
Proof.
  simpl; constructor.
  intros s s' mat [x Hx] c p; subst.
  rewrite board_act.
  rewrite count_act.
  apply mat.
Qed.

Definition certified_Chess_TB : OCamlTablebase ChessGame :=
  certified_TB.

(*
Print Assumptions certified_Chess_TB.
*)
