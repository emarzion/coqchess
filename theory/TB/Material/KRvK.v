Require Import List.
Import ListNotations.

Require Import Games.Game.Player.
Require Import Chess.TB.Material.Material.
Require Import Chess.Chess.

Definition KRvK : material :=
  fun c p =>
    match c, p with
    | White, King => 1
    | Black, King => 1
    | White, Rook => 1
    | _, _ => 0
    end.

Definition B_checkmates : list ChessState :=
  [].

Lemma B_checkmates_correct1 : forall s,
  In s B_checkmates ->
  atomic_chess_res s = Some (Game.Win Black).
Proof.
  intros ? [].
Qed.

Lemma B_checkmates_correct2 : forall s,
  atomic_chess_res s = Some (Game.Win Black) ->
  material_eq KRvK s ->
  In s B_checkmates.
Admitted.

Lemma B_checkmates_correct3 :
  Forall (material_eq KRvK) B_checkmates.
Proof.
  constructor.
Qed.

Definition W_checkmates : list ChessState.
Admitted.

Lemma W_checkmates_correct1 : forall s,
  In s W_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Admitted.

Lemma W_checkmates_correct2 : forall s,
  atomic_chess_res s = Some (Game.Win White) ->
  material_eq KRvK s ->
  In s W_checkmates.
Admitted.

Lemma W_checkmates_correct3 :
  Forall (material_eq KRvK) W_checkmates.
Admitted.
