Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.
Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.VecRev.
Require Import Chess.Util.MatAction.
Require Import Chess.Util.PosAction.

Require Import Chess.Chess.Chess.
Require Import Chess.Util.UIP.

Lemma maccess_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess (x @ c) (x @ M) = maccess c M.
Proof.
  destruct c as [i j].
  destruct x; simpl.
  - reflexivity.
  - rewrite maccess_transpose.
    rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_vreflect.
    rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_hreflect.
    apply maccess_transpose.
  - rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_vreflect.
    reflexivity.
  - rewrite maccess_transpose.
    reflexivity.
  - rewrite maccess_hreflect.
    rewrite maccess_transpose.
    rewrite maccess_hreflect.
    reflexivity.
Qed.

Lemma maccess_mat_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess c (x @ M) = maccess (inv x @ c) M.
Proof.
  rewrite <- (act_id c) at 1.
  rewrite <- inv_right with (x := x).
  rewrite <- act_assoc.
  apply maccess_act.
Qed.

Lemma maccess_coord_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess (x @ c) M = maccess c (inv x @ M).
Proof.
  rewrite <- (act_id M) at 1.
  rewrite <- inv_right with (x := x).
  rewrite <- act_assoc.
  apply maccess_act.
Qed.

Lemma val_inr {n} (i : Fin.Fin n) : Fin.val (inr i : Fin.Fin (S n)) = S (Fin.val i).
Proof.
  reflexivity.
Qed.

Lemma val_last {n} : Fin.val (Fin.last : Fin.Fin (S n)) = n.
Proof.
  induction n.
  - reflexivity.
  - simpl Fin.last.
    rewrite @val_inr.
    congruence.
Qed.

Lemma val_front {n} (i : Fin.Fin n) : Fin.val (Fin.front i) =
  Fin.val i.
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + destruct n.
      * destruct j.
      * rewrite Fin.front_inr.
        rewrite val_inr.
        rewrite IHn; auto.
Qed.

Lemma val_Fin_rev {n} (i : Fin.Fin (S n)) : Fin.val (Fin.Fin_rev i) = n - Fin.val i.
Proof.
  induction n.
  - destruct i as [[]|[]].
    reflexivity.
  - destruct i as [[]|j].
    + rewrite Fin.Fin_rev_inl.
      rewrite val_last.
      reflexivity.
    + rewrite Fin.Fin_rev_inr.
      rewrite val_front.
      rewrite IHn; reflexivity.
Qed.

Lemma dist_refl : forall n, Dist.dist n n = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; auto.
Qed.

Lemma dist_sub n : forall k, k <= n ->
  Dist.dist n k = n - k.
Proof.
  induction n; intros k Hk.
  - simpl.
    inversion Hk; auto.
  - inversion Hk.
    + rewrite dist_refl.
      rewrite PeanoNat.Nat.sub_diag; auto.
    + destruct k.
      * reflexivity.
      * simpl.
        apply IHn.
        apply le_S_n; auto.
Qed.

Lemma dist_n_sub_n_sub : forall n x y,
  x <= n -> y <= n ->
  Dist.dist (n - x) (n - y) = Dist.dist x y.
Proof.
  induction n; intros x y Hx Hy.
  - inversion Hx; inversion Hy.
    reflexivity.
  - inversion Hx; inversion Hy.
    + simpl.
      do 2 rewrite dist_refl; auto.
    + rewrite PeanoNat.Nat.sub_diag.
      rewrite Dist.dist_sym.
      rewrite Dist.dist_n_0.
      rewrite dist_sub; auto.
    + rewrite PeanoNat.Nat.sub_diag.
      rewrite Dist.dist_n_0.
      rewrite Dist.dist_sym.
      rewrite dist_sub; auto.
    + rewrite PeanoNat.Nat.sub_succ_l; auto.
      rewrite PeanoNat.Nat.sub_succ_l; auto.
      simpl.
      apply IHn; auto.
Qed.

Lemma val_bound {n} (i : Fin.Fin n) :
  Fin.val i < n.
Proof.
  induction n.
  - destruct i.
  - destruct i as [|j].
    + simpl.
      apply PeanoNat.Nat.lt_0_succ.
    + rewrite val_inr.
      apply Arith_base.lt_n_S_stt.
      apply IHn.
Qed.

Lemma Fin_dist_Fin_rev {n} (i j : Fin.Fin n) :
  Fin.fin_dist (Fin.Fin_rev i) (Fin.Fin_rev j) =
  Fin.fin_dist i j.
Proof.
  destruct n.
  - destruct i.
  - unfold Fin.fin_dist.
    do 2 rewrite val_Fin_rev.
    rewrite dist_n_sub_n_sub; auto;
      apply PeanoNat.lt_n_Sm_le; apply val_bound.
Qed.

(* stabilizes the orientation of lines *)
Definition stable (x : d8_group) : bool :=
  match x with
  | i | r180 | h | v => true
  | _ => false
  end.

Lemma stable_inv : forall x, stable (inv x) = stable x.
Proof.
  destruct x; auto.
Qed.

Require Import Lia.

Lemma fin_sbetween_rev {n} (i j k : Fin.Fin n) :
  Fin.fin_sbetween i j k ->
  Fin.fin_sbetween (Fin.Fin_rev i) (Fin.Fin_rev j) (Fin.Fin_rev k).
Proof.
  destruct n.
  - destruct i.
  - pose proof (val_bound i) as Hi.
    pose proof (val_bound j) as Hj.
    pose proof (val_bound k) as Hk.
    intros [[pf1 pf2]|[pf1 pf2]].
    + right; split; do 2 rewrite @val_Fin_rev; lia.
    + left; split; do 2 rewrite @val_Fin_rev; lia.
Qed.

Lemma fin_sbetween_fst_stable {n} (x : d8_group)
  (c1 c2 c3 : Coord n n) :
  stable x = true ->
  Fin.fin_sbetween (fst c1) (fst c2) (fst c3) ->
  Fin.fin_sbetween (fst (x @ c1)) (fst (x @ c2)) (fst (x @ c3)).
Proof.
  intros x_stab pf.
  destruct c1 as [i1 j1].
  destruct c2 as [i2 j2].
  destruct c3 as [i3 j3].
  destruct x; try discriminate; simpl act; simpl pos_act;
    simpl fst in *; simpl snd in *.
  - auto.
  - apply fin_sbetween_rev; auto.
  - apply fin_sbetween_rev; auto.
  - auto.
Qed.

Lemma fin_sbetween_snd_stable {n} (x : d8_group)
  (c1 c2 c3 : Coord n n) :
  stable x = true ->
  Fin.fin_sbetween (snd c1) (snd c2) (snd c3) ->
  Fin.fin_sbetween (snd (x @ c1)) (snd (x @ c2)) (snd (x @ c3)).
Proof.
  intros x_stab pf.
  destruct c1 as [i1 j1].
  destruct c2 as [i2 j2].
  destruct c3 as [i3 j3].
  destruct x; try discriminate; simpl act; simpl pos_act;
    simpl fst in *; simpl snd in *.
  - auto.
  - apply fin_sbetween_rev; auto.
  - auto.
  - apply fin_sbetween_rev; auto.
Qed.

Lemma fin_sbetween_fst_snd_unstable {n} (x : d8_group)
  (c1 c2 c3 : Coord n n) :
  stable x = false ->
  Fin.fin_sbetween (fst c1) (fst c2) (fst c3) ->
  Fin.fin_sbetween (snd (x @ c1)) (snd (x @ c2)) (snd (x @ c3)).
Proof.
  intros x_unstab pf.
  destruct c1 as [i1 j1].
  destruct c2 as [i2 j2].
  destruct c3 as [i3 j3].
  destruct x; try discriminate; simpl act; simpl pos_act;
    simpl fst in *; simpl snd in *.
  - apply fin_sbetween_rev; auto.
  - auto.
  - auto.
  - apply fin_sbetween_rev; auto.
Qed.

Lemma fin_sbetween_snd_fst_unstable {n} (x : d8_group)
  (c1 c2 c3 : Coord n n) :
  stable x = false ->
  Fin.fin_sbetween (snd c1) (snd c2) (snd c3) ->
  Fin.fin_sbetween (fst (x @ c1)) (fst (x @ c2)) (fst (x @ c3)).
Proof.
  intros x_unstab pf.
  destruct c1 as [i1 j1].
  destruct c2 as [i2 j2].
  destruct c3 as [i3 j3].
  destruct x; try discriminate; simpl act; simpl pos_act;
    simpl fst in *; simpl snd in *.
  - auto.
  - apply fin_sbetween_rev; auto.
  - auto.
  - apply fin_sbetween_rev; auto.
Qed.

Lemma neighbor_adj_act (b : Board) (p p' : Pos)
  (x : d8_group) :
  neighbor_adj b p p' ->
  neighbor_adj (x @ b) (x @ p) (x @ p').
Proof.
  unfold neighbor_adj.
  unfold neighbor_preadj.
  unfold rank_dist, file_dist, rank, file.
  destruct p as [i j].
  destruct p' as [i' j'].
  destruct x; unfold act; unfold d8_coord_action;
    unfold pos_act; unfold fst; unfold snd;
    repeat rewrite Fin_dist_Fin_rev; tauto.
Qed.

Lemma horiz_preadj_stable (x : d8_group)
  (p1 p2 : Pos) :
  stable x = true ->
  horiz_preadj p1 p2 ->
  horiz_preadj (x @ p1) (x @ p2).
Proof.
  unfold horiz_preadj.
  intros x_stab pf1.
  destruct p1 as [i1 j1].
  destruct p2 as [i2 j2].
  destruct x; try discriminate; unfold act;
    unfold d8_coord_action; unfold pos_act;
    unfold rank in *; unfold snd in *;
    congruence.
Qed.

Lemma vert_preadj_stable (x : d8_group)
  (p1 p2 : Pos) :
  stable x = true ->
  vert_preadj p1 p2 ->
  vert_preadj (x @ p1) (x @ p2).
Proof.
  unfold vert_preadj.
  intros x_stab pf1.
  destruct p1 as [i1 j1].
  destruct p2 as [i2 j2].
  destruct x; try discriminate; unfold act;
    unfold d8_coord_action; unfold pos_act;
    unfold file in *; unfold fst in *;
    congruence.
Qed.

Lemma horiz_vert_preadj_unstable (x : d8_group)
  (p1 p2 : Pos) :
  stable x = false ->
  horiz_preadj p1 p2 ->
  vert_preadj (x @ p1) (x @ p2).
Proof.
  unfold vert_preadj.
  unfold horiz_preadj.
  intros x_stab pf1.
  destruct p1 as [i1 j1].
  destruct p2 as [i2 j2].
  destruct x; try discriminate; unfold act;
    unfold d8_coord_action; unfold pos_act;
    unfold rank in *; unfold snd in *;
    unfold file in *; unfold fst in *;
    congruence.
Qed.

Lemma vert_horiz_preadj_unstable (x : d8_group)
  (p1 p2 : Pos) :
  stable x = false ->
  vert_preadj p1 p2 ->
  horiz_preadj (x @ p1) (x @ p2).
Proof.
  unfold vert_preadj.
  unfold horiz_preadj.
  intros x_stab pf1.
  destruct p1 as [i1 j1].
  destruct p2 as [i2 j2].
  destruct x; try discriminate; unfold act;
    unfold d8_coord_action; unfold pos_act;
    unfold rank in *; unfold snd in *;
    unfold file in *; unfold fst in *;
    congruence.
Qed.

Lemma horiz_adj_stable (x : d8_group)
  (p1 p2 : Pos) (b : Board) :
  stable x = true ->
  horiz_adj b p1 p2 ->
  horiz_adj (x @ b) (x @ p1) (x @ p2).
Proof.
  intros x_stab [pf1 pf2]; split.
  - apply horiz_preadj_stable; auto.
  - intros p3 pf3 pf4.
    rewrite <- (act_id p3).
    rewrite <- (inv_right _ x).
    rewrite <- act_assoc.
    unfold lookup_piece.
    rewrite @maccess_act.
    apply pf2.
    + apply horiz_preadj_stable with (x := inv x) in pf3.
      * rewrite act_assoc in pf3.
        rewrite inv_left in pf3.
        rewrite act_id in pf3; auto.
      * rewrite stable_inv; auto.
    + apply fin_sbetween_fst_stable with (x := inv x) in pf4.
      * do 2 rewrite act_assoc in pf4.
        rewrite inv_left in pf4.
        do 2 rewrite act_id in pf4; auto.
      * rewrite stable_inv; auto.
Qed.

Lemma vert_adj_stable (x : d8_group)
  (p1 p2 : Pos) (b : Board) :
  stable x = true ->
  vert_adj b p1 p2 ->
  vert_adj (x @ b) (x @ p1) (x @ p2).
Proof.
  intros x_stab [pf1 pf2]; split.
  - apply vert_preadj_stable; auto.
  - intros p3 pf3 pf4.
    rewrite <- (act_id p3).
    rewrite <- (inv_right _ x).
    rewrite <- act_assoc.
    unfold lookup_piece.
    rewrite @maccess_act.
    apply pf2.
    + apply vert_preadj_stable with (x := inv x) in pf3.
      * rewrite act_assoc in pf3.
        rewrite inv_left in pf3.
        rewrite act_id in pf3; auto.
      * rewrite stable_inv; auto.
    + apply fin_sbetween_snd_stable with (x := inv x) in pf4.
      * do 2 rewrite act_assoc in pf4.
        rewrite inv_left in pf4.
        do 2 rewrite act_id in pf4; auto.
      * rewrite stable_inv; auto.
Qed.

Lemma horiz_vert_adj_unstable (x : d8_group)
  (p1 p2 : Pos) (b : Board) :
  stable x = false ->
  horiz_adj b p1 p2 ->
  vert_adj (x @ b) (x @ p1) (x @ p2).
Proof.
  intros x_unstab [pf1 pf2]; split.
  - apply horiz_vert_preadj_unstable; auto.
  - intros p3 pf3 pf4.
    rewrite <- (act_id p3).
    rewrite <- (inv_right _ x).
    rewrite <- act_assoc.
    unfold lookup_piece.
    rewrite @maccess_act.
    apply pf2.
    + apply vert_horiz_preadj_unstable with (x := inv x) in pf3.
      * rewrite act_assoc in pf3.
        rewrite inv_left in pf3.
        rewrite act_id in pf3; auto.
      * rewrite stable_inv; auto.
    + apply fin_sbetween_snd_fst_unstable with (x := inv x) in pf4.
      * do 2 rewrite act_assoc in pf4.
        rewrite inv_left in pf4.
        do 2 rewrite act_id in pf4; auto.
      * rewrite stable_inv; auto.
Qed.

Lemma vert_horiz_adj_unstable (x : d8_group)
  (p1 p2 : Pos) (b : Board) :
  stable x = false ->
  vert_adj b p1 p2 ->
  horiz_adj (x @ b) (x @ p1) (x @ p2).
Proof.
  intros x_unstab [pf1 pf2]; split.
  - apply vert_horiz_preadj_unstable; auto.
  - intros p3 pf3 pf4.
    rewrite <- (act_id p3).
    rewrite <- (inv_right _ x).
    rewrite <- act_assoc.
    unfold lookup_piece.
    rewrite @maccess_act.
    apply pf2.
    + apply horiz_vert_preadj_unstable with (x := inv x) in pf3.
      * rewrite act_assoc in pf3.
        rewrite inv_left in pf3.
        rewrite act_id in pf3; auto.
      * rewrite stable_inv; auto.
    + apply fin_sbetween_fst_snd_unstable with (x := inv x) in pf4.
      * do 2 rewrite act_assoc in pf4.
        rewrite inv_left in pf4.
        do 2 rewrite act_id in pf4; auto.
      * rewrite stable_inv; auto.
Qed.

Lemma orthog_adj_act (b : Board) (p p' : Pos)
  (x : d8_group) :
  orthog_adj b p p' ->
  orthog_adj (x @ b) (x @ p) (x @ p').
Proof.
  intros [h|v].
  - destruct (stable x) eqn:x_stab.
    + left; apply horiz_adj_stable; auto.
    + right; apply horiz_vert_adj_unstable; auto.
  - destruct (stable x) eqn:x_stab.
    + right; apply vert_adj_stable; auto.
    + left; apply vert_horiz_adj_unstable; auto.
Qed.

Lemma diag_preadj_act (p p' : Pos)
  (x : d8_group) :
  diag_preadj p p' ->
  diag_preadj (x @ p) (x @ p').
Proof.
  unfold diag_preadj.
  unfold rank_dist, file_dist, rank, file.
  destruct p as [i j].
  destruct p' as [i' j'].
  destruct x; unfold act; unfold d8_coord_action;
    unfold pos_act; unfold fst; unfold snd;
    repeat rewrite Fin_dist_Fin_rev; firstorder.
Qed.

Lemma diag_adj_act (b : Board) (p p' : Pos)
  (x : d8_group) :
  diag_adj b p p' ->
  diag_adj (x @ b) (x @ p) (x @ p').
Proof.
  intros [pf1 pf2]; split.
  - apply diag_preadj_act; auto.
  - intros p3 H1 H2 H3.
    unfold lookup_piece.
    rewrite @maccess_mat_act.
    apply pf2.
    + apply diag_preadj_act with (x := inv x) in H1.
      rewrite act_assoc in H1.
      rewrite inv_left in H1.
      rewrite act_id in H1; auto.
    + destruct (stable (inv x)) eqn:x_stab.
      * apply fin_sbetween_fst_stable with (x := inv x) in H2; auto.
        do 2 rewrite act_assoc in H2.
        rewrite inv_left in H2.
        do 2 rewrite act_id in H2; auto.
      * apply fin_sbetween_snd_fst_unstable with (x := inv x) in H3; auto.
        do 2 rewrite act_assoc in H3.
        rewrite inv_left in H3.
        do 2 rewrite act_id in H3; auto.
    + destruct (stable (inv x)) eqn:x_stab.
      * apply fin_sbetween_snd_stable with (x := inv x) in H3; auto.
        do 2 rewrite act_assoc in H3.
        rewrite inv_left in H3.
        do 2 rewrite act_id in H3; auto.
      * apply fin_sbetween_fst_snd_unstable with (x := inv x) in H2; auto.
        do 2 rewrite act_assoc in H2.
        rewrite inv_left in H2.
        do 2 rewrite act_id in H2; auto.
Qed.

Lemma diag_orthog_adj_act (b : Board) (p p' : Pos)
  (x : d8_group) :
  diag_orthog_adj b p p' ->
  diag_orthog_adj (x @ b) (x @ p) (x @ p').
Proof.
  unfold diag_orthog_adj.
  intros [d|o].
  - left; now apply diag_adj_act.
  - right; now apply orthog_adj_act.
Qed.

Lemma L_adj_act (b : Board) (p p' : Pos)
  (x : d8_group) :
  L_adj b p p' ->
  L_adj (x @ b) (x @ p) (x @ p').
Proof.
  unfold L_adj.
  unfold L_preadj.
  unfold rank_dist, file_dist, rank, file.
  destruct p as [i j].
  destruct p' as [i' j'].
  destruct x; unfold act; unfold d8_coord_action;
    unfold pos_act; unfold fst; unfold snd;
    repeat rewrite Fin_dist_Fin_rev; tauto.
Qed.

Lemma non_pawn_piece_adj_act (b : Board) (piece : Piece) (p p' : Pos)
  (x : d8_group) :
  non_pawn_piece_adj piece b p p' ->
  non_pawn_piece_adj piece (x @ b) (x @ p) (x @ p').
Proof.
  destruct piece.
  - apply neighbor_adj_act.
  - apply diag_orthog_adj_act.
  - apply orthog_adj_act.
  - apply diag_adj_act.
  - apply L_adj_act.
Qed.

Definition state_act (x : d8_group) (s : ChessState) : ChessState.
Proof.
  refine {|
    chess_to_play := chess_to_play s;
    board := x @ board s;
    white_king := x @ white_king s;
    black_king := x @ black_king s;
    lookup_white_king := _;
    lookup_black_king := _;
    kings_unique := _;
    opp_to_play_not_in_check := _;
  |}.
  - unfold lookup_piece.
    rewrite @maccess_act.
    apply s.
  - unfold lookup_piece.
    rewrite @maccess_act.
    apply s.
  - intros pl pos pf.
    unfold lookup_piece in pf.
    rewrite @maccess_mat_act in pf.
    apply s in pf.
    destruct pl; simpl king in *.
    + rewrite <- pf.
      rewrite act_assoc.
      rewrite inv_right.
      rewrite act_id; auto.
    + rewrite <- pf.
      rewrite act_assoc.
      rewrite inv_right.
      rewrite act_id; auto.
  - intros pos pf1.
    unfold lookup_piece in pf1.
    rewrite @maccess_mat_act in pf1.
    apply opp_to_play_not_in_check in pf1.
    intro pf2; apply pf1.
    unfold is_threatened_by in pf2.
    destruct pf2 as [pos' [piece [Hlookup Hadj]]].
    exists (inv x @ pos'), piece; split.
    + unfold lookup_piece in *.
      rewrite @maccess_mat_act in Hlookup; auto.
    + apply non_pawn_piece_adj_act with (x := inv x) in Hadj.
      rewrite act_assoc in Hadj.
      rewrite inv_left in Hadj.
      rewrite act_id in Hadj; auto.
Defined.

Lemma state_ext (s s' : ChessState) :
  chess_to_play s = chess_to_play s' ->
  board s = board s' ->
  white_king s = white_king s' ->
  black_king s = black_king s' ->
  s = s'.
Proof.
  intros.
  destruct s, s'; simpl in *.
  subst.
  f_equal; apply UIP.
Qed.

Lemma state_act_id (s : ChessState) : state_act i s = s.
Proof.
  apply state_ext; simpl.
  - auto.
  - auto.
  - apply pos_act_id.
  - apply pos_act_id.
Qed.

Lemma state_act_assoc (x y : d8_group) (s : ChessState) :
  state_act x (state_act y s) = state_act (x # y) s.
Proof.
  apply state_ext; simpl.
  - auto.
  - apply mat_act_assoc.
  - apply pos_act_assoc.
  - apply pos_act_assoc.
Qed.

Global Instance state_action : GroupAction d8_group ChessState := {|
  act := state_act;
  act_id := state_act_id;
  act_assoc := state_act_assoc;
  |}.
