Require Import Arith.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import Chess.Util.Fin.

Require Import Games.Game.Player.
Require Import Chess.TB.Material.Material.
Require Import Chess.Chess.
Require Import Chess.TB.Material.OnlyKing.

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
Proof.
  intros s Hs1 Hs2.
  exfalso; elim only_king_cannot_checkmate
    with (s := s) (c := Black); auto.
  intro; apply Hs2.
Qed.

Lemma B_checkmates_correct3 :
  Forall (material_eq KRvK) B_checkmates.
Proof.
  constructor.
Qed.

Record PreChessState : Type := {
  pre_chess_to_play : Player;
  pre_board : Board;
  pre_white_king : Pos;
  pre_black_king : Pos;
  pre_king pl :=
    match pl with
    | White => pre_white_king
    | Black => pre_black_king
    end
  }.

Definition pre_lookup_white_king
  (s : PreChessState) : Prop :=
  lookup_piece (pre_white_king s) (pre_board s)
  = Some (White, King).

Definition pre_lookup_black_king
  (s : PreChessState) : Prop :=
  lookup_piece (pre_black_king s) (pre_board s)
  = Some (Black, King).

Definition pre_kings_unique
  (s : PreChessState) : Prop := forall player pos,
  lookup_piece pos (pre_board s) = Some (player, King) ->
  pos = pre_king s player.

Definition pre_opp_to_play_not_in_check
  (s : PreChessState) : Prop := forall pos,
  lookup_piece pos (pre_board s) =
  Some (opp (pre_chess_to_play s), King) ->
  ~ is_threatened_by (pre_board s) pos (pre_chess_to_play s).

Fixpoint mk_ChessStates (l : list PreChessState) :
  Forall pre_lookup_white_king l ->
  Forall pre_lookup_black_king l ->
  Forall pre_kings_unique l ->
  Forall pre_opp_to_play_not_in_check l ->
  list ChessState :=
  match l with
  | [] => fun _ _ _ _ => []
  | s :: l' => fun pf1 pf2 pf3 pf4 =>
      {|
        chess_to_play := pre_chess_to_play s;
        board := pre_board s;
        white_king := pre_white_king s;
        black_king := pre_black_king s;
        lookup_white_king := Forall_inv pf1;
        lookup_black_king := Forall_inv pf2;
        kings_unique := Forall_inv pf3;
        opp_to_play_not_in_check := Forall_inv pf4;
      |} ::
    (mk_ChessStates l'
      (Forall_inv_tail pf1)
      (Forall_inv_tail pf2)
      (Forall_inv_tail pf3)
      (Forall_inv_tail pf4)
    )
  end.

Inductive check_type : Type :=
  | vert : check_type
  | horiz : check_type.

Record corner_config : Type :=  mk_config {
  corner : Pos;
  off_corner : Pos;
  check : check_type
  }.

Definition corner_king_configs : list corner_config :=
  [ (mk_config (file_a, rank_1) (file_b, rank_3) horiz);
    (mk_config (file_a, rank_1) (file_c, rank_2) vert);
    (mk_config (file_a, rank_8) (file_b, rank_6) horiz);
    (mk_config (file_a, rank_8) (file_c, rank_7) vert);
    (mk_config (file_h, rank_1) (file_g, rank_3) horiz);
    (mk_config (file_h, rank_1) (file_f, rank_2) vert);
    (mk_config (file_h, rank_8) (file_g, rank_6) horiz);
    (mk_config (file_h, rank_8) (file_f, rank_7) vert)
  ].

Ltac destruct_or :=
  match goal with
  | [ H : ?P \/ ?Q |- _ ] => destruct H as [H|H]; destruct_or
  | [ H : False |- _ ] => destruct H
  | _ => idtac
  end.

Lemma corner_off_corner_neq : forall cfg,
  In cfg corner_king_configs ->
  corner cfg <> off_corner cfg.
Proof.
  unfold corner_king_configs; intros cfg pf.
  simpl in pf.
  destruct_or; subst; simpl; discriminate.
Qed.

Definition at_least_two_away {n} (i : Fin n) : list (Fin n) :=
  List.filter (fun j =>
    if Compare_dec.le_dec 2 (fin_dist i j) then true else false)
    (all_fin n).

Definition empty_board : Board :=
  Mat.mreplicate None.

Fixpoint place_pieces (l : list ((Player * Piece) * Pos)) : Board :=
  match l with
  | [] => empty_board
  | ((c,p),pos) :: l' =>
    place_piece c p pos (place_pieces l')
  end.

Fixpoint list_count {X} `{Dec.Discrete X} (x : X)
  (l : list X) : nat :=
  match l with
  | [] => 0
  | y :: l' =>
    if Dec.eq_dec x y then S (list_count x l') else list_count x l'
  end.

Definition W_corner_pre_checkmates : list PreChessState.
Proof.
  refine (flat_map (fun cfg => _) corner_king_configs).
  refine (match check cfg with
          | vert => _
          | horiz => _
          end).
  - refine (map (fun i => _) (at_least_two_away (rank (corner cfg)))).
    pose (bk := corner cfg).
    pose (wk := off_corner cfg).
    pose (wr := (file (corner cfg), i)).
    pose (b :=
      place_pieces [
        ((White, King), wk);
        ((Black, King), bk);
        ((White, Rook), wr)
      ]).
    exact {|
      pre_chess_to_play := Black;
      pre_board := b;
      pre_white_king := wk;
      pre_black_king := bk;
      |}.
  - refine (map (fun i => _) (at_least_two_away (file (corner cfg)))).
    pose (bk := corner cfg).
    pose (wk := off_corner cfg).
    pose (wr := (i, rank (corner cfg))).
    pose (b :=
      place_pieces [
        ((White, King), wk);
        ((Black, King), bk);
        ((White, Rook), wr)
      ]).
    exact {|
      pre_chess_to_play := Black;
      pre_board := b;
      pre_white_king := wk;
      pre_black_king := bk;
      |}.
Defined.

Lemma W_corner_pre_checkmates_correct1 :
  Forall pre_lookup_white_king W_corner_pre_checkmates.
Proof.
  unfold W_corner_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (check cfg) eqn:Hchk.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_white_king; simpl.
    rewrite lookup_place_eq; auto.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_white_king; simpl.
    rewrite lookup_place_eq; auto.
Qed.

Lemma W_corner_pre_checkmates_correct2 :
  Forall pre_lookup_black_king W_corner_pre_checkmates.
Proof.
  unfold W_corner_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (check cfg) eqn:Hchk.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_black_king; simpl.
    rewrite lookup_place_neq.
    + rewrite lookup_place_eq; auto.
    + apply corner_off_corner_neq; auto.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_black_king; simpl.
    rewrite lookup_place_neq.
    + rewrite lookup_place_eq; auto.
    + apply corner_off_corner_neq; auto.
Qed.

Lemma vaccess_vreplicate {X} {n} (x : X) (i : Fin.Fin n) :
  Vec.vaccess i (Vec.vreplicate x) = x.
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + apply IHn.
Qed.

Lemma maccess_mreplicate {X} {m n} (x : X) (c : Mat.Coord m n) :
  Mat.maccess c (Mat.mreplicate x) = x.
Proof.
  destruct c as [i j].
  unfold Mat.mreplicate.
  unfold Mat.maccess; simpl.
  do 2 rewrite vaccess_vreplicate.
  auto.
Qed.

Lemma lookup_piece_empty (pos : Pos) :
  lookup_piece pos empty_board = None.
Proof.
  apply maccess_mreplicate.
Qed.

Ltac lookup_piece_inversion :=
  match goal with
  | [ H : lookup_piece ?pos (place_piece ?c ?p ?pos' ?b) = ?o |- _ ] =>
    let pf := fresh "pf" in
    destruct (Dec.eq_dec pos pos') as [pf|pf];
    [ rewrite pf in *; rewrite lookup_place_eq in H
    | rewrite lookup_place_neq in H; auto; lookup_piece_inversion
    ]
  | [ H : lookup_piece ?pos (clear ?pos' ?b) = ?o |- _ ] =>
    let pf := fresh "pf" in
    destruct (Dec.eq_dec pos pos') as [pf|pf];
    [ rewrite pf in *; rewrite lookup_clear_eq in H
    | rewrite lookup_clear_neq in H; auto; lookup_piece_inversion
    ]
  | [ H : lookup_piece ?pos empty_board = ?o |- _ ] =>
    rewrite lookup_piece_empty in H
  | _ => idtac
  end.

Lemma W_corner_pre_checkmates_correct3 :
  Forall pre_kings_unique W_corner_pre_checkmates.
Proof.
  unfold W_corner_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (check cfg) eqn:Hchk.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_kings_unique; simpl.
    intros [] p; simpl.
    + intro pf.
      lookup_piece_inversion;
      (reflexivity || discriminate).
    + intro pf.
      lookup_piece_inversion;
      (reflexivity || discriminate).
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_kings_unique; simpl.
    intros [] p; simpl.
    + intro pf.
      lookup_piece_inversion;
      (reflexivity || discriminate).
    + intro pf.
      lookup_piece_inversion;
      (reflexivity || discriminate).
Qed.

Lemma corner_king_configs_kings_do_not_touch : forall cfg,
  In cfg corner_king_configs ->
  ~ neighbor_preadj (corner cfg) (off_corner cfg).
Proof.
  intros cfg pf.
  unfold corner_king_configs in pf.
  simpl in pf.
  destruct_or; subst; compute; lia.
Qed.

Lemma corner_king_configs_off_corner_corner_neq : forall cfg,
  In cfg corner_king_configs ->
  off_corner cfg <> corner cfg.
Proof.
  intros cfg pf.
  unfold corner_king_configs in pf.
  simpl in pf.
  destruct_or; subst; compute;
  discriminate.
Qed.

Lemma corner_king_configs_off_corner_corner_file_neq : forall cfg,
  In cfg corner_king_configs ->
  file (off_corner cfg) <> file (corner cfg).
Proof.
  intros cfg pf.
  unfold corner_king_configs in pf.
  simpl in pf.
  destruct_or; subst; compute;
  discriminate.
Qed.

Lemma corner_king_configs_off_corner_corner_rank_neq : forall cfg,
  In cfg corner_king_configs ->
  rank (off_corner cfg) <> rank (corner cfg).
Proof.
  intros cfg pf.
  unfold corner_king_configs in pf.
  simpl in pf.
  destruct_or; subst; compute;
  discriminate.
Qed.

Lemma W_corner_pre_checkmates_correct4 :
  Forall pre_opp_to_play_not_in_check W_corner_pre_checkmates.
Proof.
  unfold W_corner_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (check cfg) eqn:Hchk.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_opp_to_play_not_in_check; simpl.
    intros pos pf1 pf2; simpl.
    lookup_piece_inversion; try discriminate.
    clear pf1.
    unfold is_threatened_by in pf2.
    destruct pf2 as [pos' [piece [pf1 pf2]]].
    lookup_piece_inversion; try discriminate.
    inversion pf1; subst.
    unfold non_pawn_piece_adj in pf2.
    unfold neighbor_adj in pf2.
    apply corner_king_configs_kings_do_not_touch in pf2; auto.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_opp_to_play_not_in_check; simpl.
    intros pos pf1 pf2; simpl.
    lookup_piece_inversion; try discriminate.
    clear pf1.
    unfold is_threatened_by in pf2.
    destruct pf2 as [pos' [piece [pf1 pf2]]].
    lookup_piece_inversion; try discriminate.
    inversion pf1; subst.
    unfold non_pawn_piece_adj in pf2.
    unfold neighbor_adj in pf2.
    apply corner_king_configs_kings_do_not_touch in pf2; auto.
Qed.

Definition W_corner_checkmates : list ChessState :=
  mk_ChessStates
    W_corner_pre_checkmates
    W_corner_pre_checkmates_correct1
    W_corner_pre_checkmates_correct2
    W_corner_pre_checkmates_correct3
    W_corner_pre_checkmates_correct4.

Definition PreChessState_of_ChessState (s : ChessState) : PreChessState := {|
  pre_chess_to_play := chess_to_play s;
  pre_board := board s;
  pre_white_king := white_king s;
  pre_black_king := black_king s;
  |}.

Lemma In_mk_ChessStates_weaken (s : ChessState)
  (l : list PreChessState) pf1 pf2 pf3 pf4 :
  In s (mk_ChessStates l pf1 pf2 pf3 pf4) ->
  In (PreChessState_of_ChessState s) l.
Proof.
  induction l; intro pf; simpl in *.
  - destruct pf.
  - destruct pf as [pf|pf].
    + left.
      rewrite <- pf.
      destruct a; auto.
    + right.
      eapply IHl; eauto.
Qed.

Lemma PreChessState_of_ChessState_pre_board s :
  pre_board (PreChessState_of_ChessState s) =
  board s.
Proof.
  reflexivity.
Qed.

Lemma PreChessState_of_ChessState_pre_chess_to_play s :
  pre_chess_to_play (PreChessState_of_ChessState s) =
  chess_to_play s.
Proof.
  reflexivity.
Qed.

Lemma lookup_piece_place_pieces l : forall p pos,
  In (p, pos) l ->
  NoDup (map snd l) ->
  lookup_piece pos (place_pieces l) = Some p.
Proof.
  induction l as [|[[c' p'] pos'] l']; intros [c p] pos pf1 pf2.
  - destruct pf1.
  - destruct pf1 as [pf1|pf1]; simpl.
    + inversion pf1.
      rewrite lookup_place_eq; auto.
    + rewrite lookup_place_neq.
      * apply IHl'; auto.
        now inversion pf2.
      * simpl in pf2.
        rewrite NoDup_cons_iff in pf2.
        destruct pf2 as [pf2 pf3].
        intro; subst.
        apply pf2.
        apply in_map with (f := snd) in pf1; auto.
Qed.

Lemma In_at_least_two_away {n} : forall (i j : Fin n),
  In j (at_least_two_away i) ->
  2 <= fin_dist i j.
Proof.
  intros i j pf.
  unfold at_least_two_away in pf.
  rewrite filter_In in pf.
  destruct pf as [_ pf].
  destruct le_dec; auto.
  discriminate.
Qed.

Lemma fin_dist_refl {n} (i : Fin n) :
  fin_dist i i = 0.
Proof.
  induction n.
  - destruct i.
  - destruct i as [|j].
    + reflexivity.
    + apply IHn.
Qed.

Lemma NoDup_cfg_file cfg i :
  In cfg corner_king_configs ->
  In i (at_least_two_away (rank (corner cfg))) ->
  NoDup [off_corner cfg; corner cfg; (file (corner cfg), i)].
Proof.
  intros pf1 pf2.
  repeat constructor.
  - intros [pf3|[pf3|[]]].
    + symmetry in pf3.
      apply corner_king_configs_off_corner_corner_neq in pf3; auto.
    + apply f_equal with (f := file) in pf3.
      simpl in pf3.
      symmetry in pf3.
      apply corner_king_configs_off_corner_corner_file_neq in pf3; auto.
  - intros [pf3|[]].
    apply f_equal with (f := rank) in pf3.
    simpl in pf3.
    rewrite <- pf3 in pf2.
    apply In_at_least_two_away in pf2.
    rewrite fin_dist_refl in pf2.
    lia.
  - intros [].
Qed.

Lemma NoDup_cfg_rank cfg i :
  In cfg corner_king_configs ->
  In i (at_least_two_away (file (corner cfg))) ->
  NoDup [off_corner cfg; corner cfg; (i, rank (corner cfg))].
Proof.
  intros pf1 pf2.
  repeat constructor.
  - intros [pf3|[pf3|[]]].
    + symmetry in pf3.
      apply corner_king_configs_off_corner_corner_neq in pf3; auto.
    + apply f_equal with (f := rank) in pf3.
      simpl in pf3.
      symmetry in pf3.
      apply corner_king_configs_off_corner_corner_rank_neq in pf3; auto.
  - intros [pf3|[]].
    apply f_equal with (f := file) in pf3.
    simpl in pf3.
    rewrite <- pf3 in pf2.
    apply In_at_least_two_away in pf2.
    rewrite fin_dist_refl in pf2.
    lia.
  - intros [].
Qed.

Definition edge_file (f : File) : Prop :=
  f = file_a \/ f = file_h.

Definition edge_rank (r : Rank) : Prop :=
  r = rank_1 \/ r = rank_8.

Definition is_corner (pos : Pos) : Prop :=
  edge_file (file pos) /\ edge_rank (rank pos).

Definition second_file (f : File) : File :=
  if Dec.eq_dec f file_a then file_b else file_g.

Definition second_rank (r : Rank) : Rank :=
  if Dec.eq_dec r rank_1 then rank_2 else rank_7.

Definition corner_neighborhood (pos : Pos) : list Pos := [
  pos;
  (file pos, second_rank (rank pos));
  (second_file (file pos), rank pos);
  (second_file (file pos), second_rank (rank pos))
  ].

Lemma dist_0 x : forall y, Dist.dist x y = 0 ->
  x = y.
Proof.
  induction x; intro y.
  - simpl. lia.
  - destruct y; simpl.
    + lia.
    + intro pf.
      apply IHx in pf; lia.
Qed.

Lemma fin_dist_0 {n} (i j : Fin.Fin n) :
  fin_dist i j = 0 -> i = j.
Proof.
  unfold fin_dist.
  intro pf.
  apply dist_0 in pf.
  apply val_inj; auto.
Qed.

Lemma pos_eq (p p' : Pos) :
  file p = file p' ->
  rank p = rank p' ->
  p = p'.
Proof.
  destruct p as [i j].
  destruct p' as [i' j'].
  simpl; congruence.
Qed.

Lemma dist_1_second_file : forall f f' : File,
  edge_file f ->
  file_dist f f' = 1 ->
  second_file f = f'.
Proof.
  intros f f' ef fd.
  unfold second_file.
  destruct Dec.eq_dec as [Heq|Hneq].
  - apply val_inj.
    simpl val at 1.
    unfold file_dist in fd.
    rewrite Heq in fd.
    unfold fin_dist in fd.
    simpl val at 1 in fd.
    rewrite Dist.dist_sym in fd.
    rewrite Dist.dist_n_0 in fd; auto.
  - destruct ef as [|ef]; [contradiction|].
    apply val_inj.
    simpl val at 1.
    unfold file_dist in fd.
    rewrite ef in fd.
    unfold fin_dist in fd.
    simpl val at 1 in fd.
    rewrite <- StateAction.dist_n_sub_n_sub with (n := 7) in fd.
    + rewrite Dist.dist_sym in fd.
      rewrite Dist.dist_n_0 in fd; lia.
    + lia.
    + pose proof (val_bound f'); lia.
Qed.

Lemma dist_1_second_rank : forall r r' : Rank,
  edge_rank r ->
  rank_dist r r' = 1 ->
  second_rank r = r'.
Proof.
  intros r r' er rd.
  unfold second_rank.
  destruct Dec.eq_dec as [Heq|Hneq].
  - apply val_inj.
    simpl val at 1.
    unfold rank_dist in rd.
    rewrite Heq in rd.
    unfold fin_dist in rd.
    simpl val at 1 in rd.
    rewrite Dist.dist_sym in rd.
    rewrite Dist.dist_n_0 in rd; auto.
  - destruct er as [|er]; [contradiction|].
    apply val_inj.
    simpl val at 1.
    unfold rank_dist in rd.
    rewrite er in rd.
    unfold fin_dist in rd.
    simpl val at 1 in rd.
    rewrite <- StateAction.dist_n_sub_n_sub with (n := 7) in rd.
    + rewrite Dist.dist_sym in rd.
      rewrite Dist.dist_n_0 in rd; lia.
    + lia.
    + pose proof (val_bound r'); lia.
Qed.

Lemma corner_neighborhood_inv : forall pos pos',
  is_corner pos -> neighbor_preadj pos pos' ->
  In pos' (corner_neighborhood pos).
Proof.
  intros pos pos' cn nb.
  destruct cn as [ef er].
  destruct nb as [nbr nbf].
  rewrite Nat.le_1_r in *.
  destruct nbr as [nbr|nbr];
  destruct nbf as [nbf|nbf].
  - unfold rank_dist, file_dist in *.
    apply fin_dist_0 in nbf, nbr.
    left; apply pos_eq; auto.
  - apply fin_dist_0 in nbr.
    right; right; left.
    apply pos_eq; auto.
    simpl.
    apply dist_1_second_file; auto.
  - apply fin_dist_0 in nbf.
    right; left.
    apply pos_eq; auto.
    simpl.
    apply dist_1_second_rank; auto.
  - right; right; right; left.
    apply pos_eq; simpl.
    + apply dist_1_second_file; auto.
    + apply dist_1_second_rank; auto.
Qed.

Lemma corner_is_corner cfg :
  In cfg corner_king_configs ->
  is_corner (corner cfg).
Proof.
  intro pf; split.
  - unfold corner_king_configs in pf.
    simpl in pf.
    destruct_or; rewrite <- pf; simpl;
      try (now left); now right.
  - unfold corner_king_configs in pf.
    simpl in pf.
    destruct_or; rewrite <- pf; simpl;
      try (now left); now right.
Qed.

Lemma file_neq (pos pos' : Pos) :
  file pos <> file pos' ->
  pos <> pos'.
Proof.
  congruence.
Qed.

Lemma rank_neq (pos pos' : Pos) :
  rank pos <> rank pos' ->
  pos <> pos'.
Proof.
  congruence.
Qed.

Lemma second_rank_dist r :
  edge_rank r ->
  rank_dist r (second_rank r) = 1.
Proof.
  intro er.
  unfold second_rank.
  destruct (Dec.eq_dec r rank_1) as [Heq|Hneq].
  - rewrite Heq; auto.
  - destruct er as [|er].
    + contradiction.
    + rewrite er; auto.
Qed.

Lemma second_file_dist f :
  edge_file f ->
  file_dist f (second_file f) = 1.
Proof.
  intro ef.
  unfold second_file.
  destruct (Dec.eq_dec f file_a) as [Heq|Hneq].
  - rewrite Heq; auto.
  - destruct ef as [|ef].
    + contradiction.
    + rewrite ef; auto.
Qed.

Lemma not_rank_sbetween_left r r' :
  ~ rank_sbetween r r r'.
Proof.
  unfold rank_sbetween.
  unfold fin_sbetween.
  unfold SBetween.sbetween.
  lia.
Qed.

Lemma not_file_sbetween_left f f' :
  ~ file_sbetween f f f'.
Proof.
  unfold file_sbetween.
  unfold fin_sbetween.
  unfold SBetween.sbetween.
  lia.
Qed.

Lemma not_rank_sbetween_right r r' :
  ~ rank_sbetween r r' r'.
Proof.
  unfold rank_sbetween.
  unfold fin_sbetween.
  unfold SBetween.sbetween.
  lia.
Qed.

Lemma not_file_sbetween_right f f' :
  ~ file_sbetween f f' f'.
Proof.
  unfold file_sbetween.
  unfold fin_sbetween.
  unfold SBetween.sbetween.
  lia.
Qed.

Lemma not_rank_sbetween_edge_second_rank r r' :
  edge_rank r' ->
  ~ rank_sbetween r r' (second_rank r').
Proof.
  intros pf.
  unfold rank_sbetween.
  unfold fin_sbetween.
  unfold SBetween.sbetween.
  unfold second_rank.
  destruct (Dec.eq_dec r' rank_1) as [Heq|Hneq].
  - rewrite Heq.
    simpl (val rank_1).
    simpl (val rank_2).
    lia.
  - destruct pf as [pf|pf]; [contradiction|].
    rewrite pf.
    simpl (val rank_8).
    simpl (val rank_7).
    pose proof (val_bound r).
    lia.
Qed.

Lemma vert_check_ranks cfg :
  In cfg corner_king_configs ->
  check cfg = vert ->
  rank_dist (rank (off_corner cfg)) (rank (corner cfg)) <= 1.
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; lia.
Qed.

Lemma vert_check_files cfg :
  In cfg corner_king_configs ->
  check cfg = vert ->
  file_dist (file (off_corner cfg)) (second_file (file (corner cfg))) <= 1.
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; lia.
Qed.

Lemma horiz_check_files cfg :
  In cfg corner_king_configs ->
  check cfg = horiz ->
  file_dist (file (off_corner cfg)) (file (corner cfg)) <= 1.
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; lia.
Qed.

Lemma horiz_check_ranks cfg :
  In cfg corner_king_configs ->
  check cfg = horiz ->
  rank_dist (rank (off_corner cfg)) (second_rank (rank (corner cfg))) <= 1.
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; lia.
Qed.

Lemma vert_check_rank_off_corner cfg :
  In cfg corner_king_configs ->
  check cfg = vert ->
  rank (off_corner cfg) = second_rank (rank (corner cfg)).
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; auto.
Qed.

Lemma horiz_check_file_off_corner cfg :
  In cfg corner_king_configs ->
  check cfg = horiz ->
  file (off_corner cfg) = second_file (file (corner cfg)).
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; auto.
Qed.

Lemma file_off_corner_corner_neq2 cfg :
  In cfg corner_king_configs ->
  check cfg = vert ->
  file (off_corner cfg) <> second_file (file (corner cfg)).
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; auto.
Qed.

Lemma rank_off_corner_corner_neq2 cfg :
  In cfg corner_king_configs ->
  check cfg = horiz ->
  rank (off_corner cfg) <> second_rank (rank (corner cfg)).
Proof.
  intros pf1 pf2.
  unfold corner_king_configs in pf1; simpl in pf1.
  destruct_or; rewrite <- pf1 in *; try discriminate; compute; auto.
Qed.

Lemma W_corner_checkmates_correct : forall s,
  In s W_corner_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Proof.
  intros s Hs.
  unfold atomic_chess_res.
  apply In_mk_ChessStates_weaken in Hs.
  unfold W_corner_pre_checkmates in Hs.
  rewrite in_flat_map in Hs.
  destruct Hs as [cfg [pf1 pf2]].
  destruct (check cfg) eqn:check_type.
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    pose proof (s_play := PreChessState_of_ChessState_pre_chess_to_play s).
    rewrite <- Hi1 in s_play.
    simpl in s_play; symmetry in s_play.
    pose proof (s_board := PreChessState_of_ChessState_pre_board s).
    rewrite <- Hi1 in s_board.
    unfold pre_board in s_board.
    symmetry in s_board.
    destruct enum_chess_moves as [|m _].
    + destruct Dec.dec as [chk|nchk].
      * rewrite s_play; auto.
      * elim nchk.
        intros bk Hbk.
        exists (file (corner cfg), i).
        exists Rook; split.
        -- rewrite s_board.
            apply lookup_piece_place_pieces.
           ++ rewrite s_play.
              right; right; left; auto.
           ++ apply NoDup_cfg_file; auto.
        -- rewrite s_board in Hbk.
           rewrite s_play in Hbk.
           simpl in Hbk.
           lookup_piece_inversion; try discriminate.
           right; split; [reflexivity|].
           intros p Hp1 Hp2.
           apply ListUtil.not_Some_None.
           intros pos Hpos.
           rewrite s_board in Hpos.
           simpl in Hpos.
           lookup_piece_inversion.
           ++ symmetry in Hp1.
              apply corner_king_configs_off_corner_corner_file_neq in Hp1; auto.
           ++ destruct Hp2; lia.
           ++ simpl in Hp2; destruct Hp2; lia.
           ++ discriminate.
    + destruct m as [r].
      pose proof (pf := dest_orig_neq r).
      destruct r as [m []].
      simpl in pf.
      rewrite s_play in *.
      rewrite s_board in *.
      simpl in origin_lookup.
      lookup_piece_inversion; try discriminate.
      inversion origin_lookup as [Hking].
      rewrite <- Hking in origin_dest_adj.
      simpl in origin_dest_adj.
      unfold neighbor_adj in origin_dest_adj.
      apply corner_neighborhood_inv in origin_dest_adj.
      * simpl in origin_dest_adj.
        destruct_or.
        -- congruence.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (file (corner cfg), i), Rook; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** right; right; now left.
                          *** apply NoDup_cfg_file; auto.
                     +++ apply rank_neq; simpl.
                         intro Hi.
                         rewrite Hi in Hi2.
                         apply In_at_least_two_away in Hi2.
                         rewrite second_rank_dist in Hi2; [lia|].
                         apply corner_is_corner; auto.
                 --- apply rank_neq; simpl.
                     intro Hi.
                     rewrite Hi in Hi2.
                     apply In_at_least_two_away in Hi2.
                     rewrite fin_dist_refl in Hi2; lia.
              ** right; split.
                 --- rewrite <- origin_dest_adj; reflexivity.
                 --- intros p Hp1 Hp2.
                     simpl in Hp2.
                     unfold vert_preadj in Hp1.
                     simpl in Hp1.
                     apply ListUtil.not_Some_None.
                     intros p' Hp'.
                     unfold updated_board in Hp'.
                     rewrite s_board in Hp'; simpl in Hp'.
                     lookup_piece_inversion; try discriminate.
                     +++ apply not_rank_sbetween_right in Hp2; auto.
                     +++ symmetry in Hp1.
apply corner_king_configs_off_corner_corner_file_neq in Hp1; auto.
                     +++ rewrite <- origin_dest_adj in Hp2.
                         simpl in Hp2.
                         apply not_rank_sbetween_edge_second_rank in Hp2; auto.
                         apply corner_is_corner; auto.
                     +++ simpl in Hp2.
                         apply not_rank_sbetween_left in Hp2; auto.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (off_corner cfg), King; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** now left.
                          *** apply NoDup_cfg_file; auto.
                     +++ apply rank_neq; simpl.
                         apply corner_king_configs_off_corner_corner_rank_neq; auto.
                 --- apply corner_king_configs_off_corner_corner_neq; auto.
              ** rewrite <- origin_dest_adj.
                 split.
                 --- apply vert_check_ranks; auto.
                 --- apply vert_check_files; auto.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (off_corner cfg), King; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** now left.
                          *** apply NoDup_cfg_file; auto.
                     +++ apply file_neq; simpl.
                         apply file_off_corner_corner_neq2; auto.
                 --- apply corner_king_configs_off_corner_corner_neq; auto.
              ** rewrite <- origin_dest_adj.
                 split.
                 --- simpl; rewrite vert_check_rank_off_corner; auto.
                     unfold rank_dist.
                     rewrite fin_dist_refl; lia.
                 --- apply vert_check_files; auto.
      * apply corner_is_corner; auto.
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    pose proof (s_play := PreChessState_of_ChessState_pre_chess_to_play s).
    rewrite <- Hi1 in s_play.
    simpl in s_play; symmetry in s_play.
    pose proof (s_board := PreChessState_of_ChessState_pre_board s).
    rewrite <- Hi1 in s_board.
    unfold pre_board in s_board.
    symmetry in s_board.
    destruct enum_chess_moves as [|m _].
    + destruct Dec.dec as [chk|nchk].
      * rewrite s_play; auto.
      * elim nchk.
        intros bk Hbk.
        exists (i, rank (corner cfg)).
        exists Rook; split.
        -- rewrite s_board.
            apply lookup_piece_place_pieces.
           ++ rewrite s_play.
              right; right; left; auto.
           ++ apply NoDup_cfg_rank; auto.
        -- rewrite s_board in Hbk.
           rewrite s_play in Hbk.
           simpl in Hbk.
           lookup_piece_inversion; try discriminate.
           left; split; [reflexivity|].
           intros p Hp1 Hp2.
           apply ListUtil.not_Some_None.
           intros pos Hpos.
           rewrite s_board in Hpos.
           simpl in Hpos.
           lookup_piece_inversion.
           ++ symmetry in Hp1.
              apply corner_king_configs_off_corner_corner_rank_neq in Hp1; auto.
           ++ destruct Hp2; lia.
           ++ simpl in Hp2; destruct Hp2; lia.
           ++ discriminate.
    + destruct m as [r].
      pose proof (pf := dest_orig_neq r).
      destruct r as [m []].
      simpl in pf.
      rewrite s_play in *.
      rewrite s_board in *.
      simpl in origin_lookup.
      lookup_piece_inversion; try discriminate.
      inversion origin_lookup as [Hking].
      rewrite <- Hking in origin_dest_adj.
      simpl in origin_dest_adj.
      unfold neighbor_adj in origin_dest_adj.
      apply corner_neighborhood_inv in origin_dest_adj.
      * simpl in origin_dest_adj.
        destruct_or.
        -- congruence.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (off_corner cfg), King; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** now left.
                          *** apply NoDup_cfg_rank; auto.
                     +++ apply file_neq; simpl.
                         apply corner_king_configs_off_corner_corner_file_neq; auto.
                 --- apply corner_king_configs_off_corner_corner_neq; auto.
              ** rewrite <- origin_dest_adj.
                 split.
                 --- apply horiz_check_ranks; auto.
                 --- apply horiz_check_files; auto.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (i, rank (corner cfg)), Rook; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** right; right; now left.
                          *** apply NoDup_cfg_rank; auto.
                     +++ apply file_neq; simpl.
                         intro Hi.
                         rewrite Hi in Hi2.
                         apply In_at_least_two_away in Hi2.
                         rewrite second_file_dist in Hi2; [lia|].
                         apply corner_is_corner; auto.
                 --- apply file_neq; simpl.
                     intro Hi.
                     rewrite Hi in Hi2.
                     apply In_at_least_two_away in Hi2.
                     rewrite fin_dist_refl in Hi2; lia.
              ** left; split.
                 --- rewrite <- origin_dest_adj; reflexivity.
                 --- intros p Hp1 Hp2.
                     simpl in Hp2.
                     unfold vert_preadj in Hp1.
                     simpl in Hp1.
                     apply ListUtil.not_Some_None.
                     intros p' Hp'.
                     unfold updated_board in Hp'.
                     rewrite s_board in Hp'; simpl in Hp'.
                     lookup_piece_inversion; try discriminate.
                     +++ apply not_rank_sbetween_right in Hp2; auto.
                     +++ symmetry in Hp1.
apply corner_king_configs_off_corner_corner_rank_neq in Hp1; auto.
                     +++ rewrite <- origin_dest_adj in Hp2.
                         simpl in Hp2.
                         apply not_rank_sbetween_edge_second_rank in Hp2; auto.
                         apply corner_is_corner; auto.
                     +++ simpl in Hp2.
                         apply not_file_sbetween_left in Hp2; auto.
        -- elim (no_resulting_check (dest m)).
           ++ unfold updated_board.
              rewrite lookup_clear_neq; [|congruence].
              rewrite lookup_place_eq; congruence.
           ++ exists (off_corner cfg), King; split.
              ** unfold updated_board.
                 rewrite pf2.
                 rewrite <- origin_dest_adj.
                 rewrite lookup_clear_neq.
                 --- rewrite lookup_place_neq.
                     +++ rewrite s_board.
                          apply lookup_piece_place_pieces.
                          *** now left.
                          *** apply NoDup_cfg_rank; auto.
                     +++ apply rank_neq; simpl.
                         apply rank_off_corner_corner_neq2; auto.
                 --- apply corner_king_configs_off_corner_corner_neq; auto.
              ** rewrite <- origin_dest_adj.
                 split.
                 --- apply horiz_check_ranks; auto.
                 --- simpl; rewrite horiz_check_file_off_corner; auto.
                     unfold file_dist.
                     rewrite fin_dist_refl; lia.
      * apply corner_is_corner; auto.
Qed.

Lemma count_place_piece pos b c p :
  lookup_piece pos b <> Some (c, p) ->
  count c p (place_piece c p pos b) =
  S (count c p b).
Proof.
  apply Mat_count_mupdate_add.
Qed.

Lemma count_place_piece_no_change pos b c c' p p' :
  lookup_piece pos b <> Some (c, p) ->
  lookup_piece pos b <> Some (c', p') ->
  (c, p) <> (c', p') ->
  count c' p' (place_piece c p pos b) =
  count c' p' b.
Proof.
  intros.
  apply Mat_count_mupdate_no_change; auto.
  congruence.
Qed.

Lemma Vec_count_vreplicate_neq {X} `{Dec.Discrete X} {n} (x y : X) :
  x <> y -> Vec_count y ((Vec.vreplicate x) : Vec.Vec X n) = 0.
Proof.
  intro.
  induction n.
  - reflexivity.
  - simpl.
    destruct Dec.eq_dec.
    + congruence.
    + auto.
Qed.

Lemma Mat_count_mreplicate_neq {X} `{Dec.Discrete X} {m n} (x y : X) :
  x <> y -> Mat_count y ((Mat.mreplicate x) : Mat.Mat X m n) = 0.
Proof.
  intros.
  unfold Mat_count.
  rewrite <- (Vec_sum_vreplicate_zero (n := m)).
  f_equal.
  apply Vec.vec_ext.
  intro i.
  rewrite MatAction.vaccess_vmap.
  unfold Mat.mreplicate.
  do 2 rewrite vaccess_vreplicate.
  apply Vec_count_vreplicate_neq; auto.
Qed.

Lemma count_empty_board : forall c p,
  count c p empty_board = 0.
Proof.
  intros c p.
  apply Mat_count_mreplicate_neq.
  discriminate.
Qed.

Lemma lookup_piece_nIn l : forall pos,
  ~ In pos (map snd l) ->
  lookup_piece pos (place_pieces l) = None.
Proof.
  induction l as [|[[] pos'] l']; intros pos pf.
  - apply lookup_piece_empty.
  - simpl.
    rewrite lookup_place_neq.
    + apply IHl'.
      intro; apply pf; now right.
    + intro; subst.
      apply pf.
      now left.
Qed.

Lemma count_place_pieces l : forall c p,
  NoDup (map snd l) ->
  count c p (place_pieces l) =
  list_count (c,p) (map fst l).
Proof.
  induction l as [|[[c' p'] pos] l']; intros c p nd.
  - apply count_empty_board.
  - simpl place_pieces.
    simpl map.
    unfold list_count.
    fold @list_count.
    destruct Dec.eq_dec as [Heq|Hneq].
    + inversion Heq.
      rewrite count_place_piece.
      * rewrite IHl'; auto.
        now inversion nd.
      * rewrite lookup_piece_nIn; [discriminate|].
        now inversion nd.
    + rewrite count_place_piece_no_change; auto.
      * apply IHl'.
        now inversion nd.
      * rewrite lookup_piece_nIn; [discriminate|].
        now inversion nd.
      * rewrite lookup_piece_nIn; [discriminate|].
        now inversion nd.
Qed.

Lemma W_corner_checkmates_mat :
  Forall (material_eq KRvK) W_corner_checkmates.
Proof.
  rewrite Forall_forall.
  intros s Hs.
  apply In_mk_ChessStates_weaken in Hs.
  unfold W_corner_pre_checkmates in Hs.
  rewrite in_flat_map in Hs.
  destruct Hs as [cfg [pf1 pf2]].
  destruct (check cfg).
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    unfold material_eq.
    rewrite <- PreChessState_of_ChessState_pre_board.
    rewrite <- Hi1.
    unfold pre_board.
    intros.
    rewrite count_place_pieces.
    + destruct c; destruct p; reflexivity.
    + simpl.
      apply NoDup_cfg_file; auto.
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    unfold material_eq.
    rewrite <- PreChessState_of_ChessState_pre_board.
    rewrite <- Hi1.
    unfold pre_board.
    intros.
    rewrite count_place_pieces.
    + destruct c; destruct p; reflexivity.
    + simpl.
      apply NoDup_cfg_rank; auto.
Qed.

Definition W_oppose_checkmates : list ChessState.
Admitted.

Lemma W_oppose_checkmates_correct : forall s,
  In s W_oppose_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Proof.
Admitted.

Lemma W_oppose_checkmates_mat :
  Forall (material_eq KRvK) W_oppose_checkmates.
Proof.
Admitted.

Definition W_checkmates : list ChessState :=
  W_corner_checkmates ++ W_oppose_checkmates.

Lemma W_checkmates_correct1 : forall s,
  In s W_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Proof.
  intros s pf.
  apply in_app_or in pf.
  destruct pf.
  - apply W_corner_checkmates_correct; auto.
  - apply W_oppose_checkmates_correct; auto.
Qed.

Lemma W_checkmates_correct2 : forall s,
  atomic_chess_res s = Some (Game.Win White) ->
  material_eq KRvK s ->
  In s W_checkmates.
Admitted.

Lemma W_checkmates_correct3 :
  Forall (material_eq KRvK) W_checkmates.
Proof.
  apply Forall_app; split.
  - apply W_corner_checkmates_mat.
  - apply W_oppose_checkmates_mat.
Qed.
