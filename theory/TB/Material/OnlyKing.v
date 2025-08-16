Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Games.Game.Player.
Require Import Chess.TB.Material.Material.
Require Import Chess.TB.MaterialPositions.
Require Import Chess.Chess.

Definition single_material : Type :=
  Piece -> nat.

Definition single_material_eq (m : single_material)
  (s : Game.GameState ChessGame) (c : Player) :=
  forall p, count c p (board s) = m p.

Definition only_king : single_material :=
  fun p =>
    match p with
    | King => 1
    | _ => 0
    end.

Lemma only_king_lookup_piece : forall s c p pos,
  single_material_eq only_king s c ->
  lookup_piece pos (board s) = Some (c, p) ->
  p = King.
Proof.
  intros s c p pos pf1 pf2.
  unfold single_material_eq in pf1.
  destruct (Games.Util.Dec.eq_dec p King); auto.
  assert (count c p (board s)  = 0) as ct.
  { rewrite pf1.
    destruct p; try reflexivity.
    contradiction.
  }
  rewrite <- mp_of_board_count in ct.
  apply mp_of_board_correct1 in pf2.
  apply ListUtil.In_length_pos in pf2.
  rewrite <- ct in pf2.
  apply Arith_base.gt_irrefl_stt in pf2.
  contradiction.
Qed.

Lemma neighbor_preadj_sym : forall pos pos',
  neighbor_preadj pos pos' ->
  neighbor_preadj pos' pos.
Proof.
  intros pos pos' pf.
  unfold neighbor_preadj in *.
  rewrite rank_dist_sym.
  rewrite (file_dist_sym (file pos') (file pos)).
  auto.
Qed.

Lemma neighbor_preadj_kings : forall s p,
  ~ neighbor_preadj (king s (opp p)) (king s p).
Proof.
  intros s p.
  pose proof (opp_to_play_not_in_check s
    (king s (opp (chess_to_play s)))
    (lookup_king s (opp (chess_to_play s)))
  ) as pf.
  unfold is_threatened_by in pf.
  intro pf'.
  apply pf.
  exists (king s (chess_to_play s)), King.
  split.
  - apply lookup_king.
  - simpl.
    unfold neighbor_adj.
    destruct (player_id_or_opp p (chess_to_play s))
      as [Heq|Heq]; rewrite <- Heq.
    + apply neighbor_preadj_sym; auto.
    + rewrite opp_invol; auto.
Qed.

Lemma only_king_cannot_checkmate : forall s c,
  single_material_eq only_king s c ->
  atomic_chess_res s <> Some (Game.Win c).
Proof.
  intros s c pf1 pf2.
  unfold atomic_chess_res in pf2.
  destruct enum_chess_moves; [|discriminate].
  destruct Games.Util.Dec.dec as [chk|]; [|discriminate].
  unfold in_check in chk.
  destruct (chk
    (king s (chess_to_play s))
    (lookup_king _ _)
    ) as [pos [p [Hp1 Hp2]]].
  inversion pf2 as [pf3].
  rewrite pf3 in Hp1.
  unfold non_pawn_piece_adj in Hp2.
  assert (p = King) as pf by
    (eapply only_king_lookup_piece; eauto).
  subst.
  unfold neighbor_adj in Hp2.
  apply kings_unique in Hp1.
  rewrite Hp1 in Hp2.
  apply neighbor_preadj_kings in Hp2; auto.
Qed.
