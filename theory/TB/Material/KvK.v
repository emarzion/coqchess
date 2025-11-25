Require Import List.
Import ListNotations.

Require Import Games.Game.Player.
Require Import Chess.TB.Material.Material.
Require Import Chess.Chess.
Require Import Chess.TB.Material.OnlyKing.

Definition KvK : material :=
  fun c p =>
    match c, p with
    | White, King => 1
    | Black, King => 1
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
  material_eq KvK s ->
  In s B_checkmates.
Proof.
  intros s Hs1 Hs2.
  exfalso; elim only_king_cannot_checkmate
    with (s := s) (c := Black); auto.
  intro; apply Hs2.
Qed.

Lemma B_checkmates_correct3 :
  Forall (material_eq KvK) B_checkmates.
Proof.
  constructor.
Qed.

Definition W_checkmates : list ChessState :=
  [].

Lemma W_checkmates_correct1 : forall s,
  In s W_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Proof.
  intros ? [].
Qed.

Lemma W_checkmates_correct2 : forall s,
  atomic_chess_res s = Some (Game.Win White) ->
  material_eq KvK s ->
  In s W_checkmates.
Proof.
  intros s Hs1 Hs2.
  exfalso; elim only_king_cannot_checkmate
    with (s := s) (c := White); auto.
  intro; apply Hs2.
Qed.

Lemma W_checkmates_correct3 :
  Forall (material_eq KvK) W_checkmates.
Proof.
  constructor.
Qed.
