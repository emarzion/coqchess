Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Games.Game.Player.
Require Import Chess.TB.Material.Material.
Require Import Chess.TB.MaterialPositions.
Require Import Chess.Chess.
Require Chess.TB.Material.KRvK.
Require Chess.TB.Material.KvK.

Definition KRvK_bound (s : Game.GameState ChessGame) : Prop :=
  material_bound KRvK.KRvK s.

Lemma KRvK_weaken : forall s,
  material_eq KRvK.KRvK s ->
  material_bound KRvK.KRvK s.
Proof.
  unfold material_eq, material_bound.
  intros s pf c p; rewrite pf; lia.
Qed.

Lemma KvK_weaken : forall s,
  material_eq KvK.KvK s ->
  material_bound KRvK.KRvK s.
Proof.
  unfold material_eq, material_bound.
  intros s pf c p; rewrite pf.
  destruct c; destruct p; simpl; lia.
Qed.

Lemma KRvK_bound_exhaustive : forall s,
  KRvK_bound s ->
  material_eq KRvK.KRvK s \/
  material_eq KvK.KvK s.
Proof.
  intros s Hs.
  unfold KRvK_bound in Hs.
  unfold material_bound in Hs.
  pose proof (Hs White Rook) as pf.
  simpl in pf.
  rewrite PeanoNat.Nat.le_1_r in pf.
  destruct pf as [wr_c|wr_c].
  - right.
    intros [] []; try (apply PeanoNat.Nat.le_0_r; apply Hs).
    + apply king_count.
    + exact wr_c.
    + apply king_count.
  - left.
    intros [] []; try (apply PeanoNat.Nat.le_0_r; apply Hs).
    + apply king_count.
    + exact wr_c.
    + apply king_count.
Qed.

Definition checkmates : Player -> list ChessState :=
  fun p =>
    match p with
    | Black => KvK.B_checkmates ++ KRvK.B_checkmates
    | White => KvK.W_checkmates ++ KRvK.W_checkmates
    end.

Lemma checkmates_correct1 : forall s p,
  In s (checkmates p) ->
  atomic_chess_res s = Some (Game.Win p).
Proof.
  intros s p Hs.
  destruct p.
  - apply in_app_or in Hs.
    destruct Hs.
    + apply KvK.W_checkmates_correct1; auto.
    + apply KRvK.W_checkmates_correct1; auto.
  - apply in_app_or in Hs.
    destruct Hs.
    + apply KvK.B_checkmates_correct1; auto.
    + apply KRvK.B_checkmates_correct1; auto.
Qed.

Lemma checkmates_correct2 : forall s p,
  atomic_chess_res s = Some (Game.Win p) ->
  KRvK_bound s ->
  In s (checkmates p).
Proof.
  intros s p Hs1 Hs2.
  apply KRvK_bound_exhaustive in Hs2.
  destruct Hs2.
  - destruct p.
    + apply in_or_app; right.
      apply KRvK.W_checkmates_correct2; auto.
    + apply in_or_app; right.
      apply KRvK.B_checkmates_correct2; auto.
  - destruct p.
    + apply in_or_app; left.
      apply KvK.W_checkmates_correct2; auto.
    + apply in_or_app; left.
      apply KvK.B_checkmates_correct2; auto.
Qed.

Lemma checkmates_correct3 : forall p,
  Forall (KRvK_bound) (checkmates p).
Proof.
  intros [].
  - apply Forall_app; split.
    + eapply Forall_impl; [| apply KvK.W_checkmates_correct3].
      apply KvK_weaken.
    + eapply Forall_impl; [| apply KRvK.W_checkmates_correct3].
      apply KRvK_weaken.
  - apply Forall_app; split.
    + eapply Forall_impl; [| apply KvK.B_checkmates_correct3].
      apply KvK_weaken.
    + eapply Forall_impl; [| apply KRvK.B_checkmates_correct3].
      apply KRvK_weaken.
Qed.
