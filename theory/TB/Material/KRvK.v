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

Lemma In_mk_ChessStates_strengthen (s : ChessState)
  (l : list PreChessState) pf1 pf2 pf3 pf4 :
  In (PreChessState_of_ChessState s) l ->
  In s (mk_ChessStates l pf1 pf2 pf3 pf4).
Proof.
  induction l; intro pf; simpl in *.
  - destruct pf.
  - destruct pf as [pf|pf].
    + left; apply StateAction.state_ext;
        simpl; rewrite pf; auto.
    + right; apply IHl; auto.
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

Lemma lookup_piece_place_pieces_Some l : forall p pos,
  In (p, pos) l ->
  exists p', lookup_piece pos (place_pieces l) = Some p'.
Proof.
  induction l as [|[[c' p'] pos'] l']; intros [c p] pos pf1.
  - destruct pf1.
  - destruct pf1 as [pf1|pf1]; simpl.
    + inversion pf1.
      rewrite lookup_place_eq; eexists; eauto.
    + destruct (Dec.eq_dec pos pos').
      * subst.
        rewrite lookup_place_eq; eexists; eauto.
      * rewrite lookup_place_neq; auto.
        apply IHl' with (p := (c, p)); auto.
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

Lemma at_least_two_away_In {n} : forall (i j : Fin n),
  2 <= fin_dist i j ->
  In j (at_least_two_away i).
Proof.
  intros i j pf.
  unfold at_least_two_away.
  rewrite filter_In.
  split; [apply all_fin_In|].
  destruct le_dec; auto.
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

Record oppose_config : Type :=  mk_oppose_config {
  edge : Pos;
  opp_check : check_type
  }.

Definition third_file (f : File) : File :=
  if Dec.eq_dec f file_a then file_c else file_f.

Definition third_rank (r : Rank) : Rank :=
  if Dec.eq_dec r rank_1 then rank_3 else rank_6.

Definition oppose_configs : list oppose_config :=
  map (fun r => {|
    edge := (file_a, r);
    opp_check := vert
  |}) (all_fin 8) ++
  map (fun r => {|
    edge := (file_h, r);
    opp_check := vert
  |}) (all_fin 8) ++
  map (fun f => {|
    edge := (f, rank_1);
    opp_check := horiz
  |}) (all_fin 8) ++
  map (fun r => {|
    edge := (r, rank_8);
    opp_check := horiz
  |}) (all_fin 8).

Definition W_oppose_pre_checkmates : list PreChessState.
Proof.
  refine (flat_map (fun cfg => _) oppose_configs).
  refine (match opp_check cfg with
          | vert => _
          | horiz => _
          end).
  - refine (map (fun i => _) (at_least_two_away (rank (edge cfg)))).
    pose (bk := edge cfg).
    pose (wk := (third_file (file (edge cfg)), rank (edge cfg))).
    pose (wr := (file (edge cfg), i)).
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
  - refine (map (fun i => _) (at_least_two_away (file (edge cfg)))).
    pose (bk := edge cfg).
    pose (wk := (file (edge cfg), third_rank (rank (edge cfg)))).
    pose (wr := (i, rank (edge cfg))).
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

Lemma W_oppose_pre_checkmates_correct1 :
  Forall pre_lookup_white_king W_oppose_pre_checkmates.
Proof.
  unfold W_oppose_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (opp_check cfg) eqn:Hchk.
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

Lemma third_file_neq f : edge_file f ->
  f <> third_file f.
Proof.
  intros pf.
  unfold third_file.
  destruct pf; destruct Dec.eq_dec; subst;
  discriminate.
Qed.

Ltac split_app :=
  match goal with
  | [ H : In ?x (?xs ++ ?ys) |- _ ] =>
      apply in_app_or in H; destruct H as [H|H]; split_app
  | _ => idtac
  end.

Lemma vert_check_edge_file cfg :
  In cfg oppose_configs ->
  opp_check cfg = vert ->
  edge_file (file (edge cfg)).
Proof.
  intros pf1 pf2.
  unfold oppose_configs in pf1.
  split_app.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now left.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now right.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now left.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now right.
Qed.

Lemma third_rank_neq r : edge_rank r ->
  r <> third_rank r.
Proof.
  intros pf.
  unfold third_rank.
  destruct pf; destruct Dec.eq_dec; subst;
  discriminate.
Qed.

Lemma horiz_check_edge_rank cfg :
  In cfg oppose_configs ->
  opp_check cfg = horiz ->
  edge_rank (rank (edge cfg)).
Proof.
  intros pf1 pf2.
  unfold oppose_configs in pf1.
  split_app.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now left.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now right.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now left.
  - rewrite in_map_iff in pf1.
    destruct pf1 as [r [Hr1 Hr2]].
    rewrite <- Hr1 in *; simpl edge in *; simpl opp_check in *.
    now right.
Qed.

Lemma W_oppose_pre_checkmates_correct2 :
  Forall pre_lookup_black_king W_oppose_pre_checkmates.
Proof.
  unfold W_oppose_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (opp_check cfg) eqn:Hchk.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_black_king; simpl.
    rewrite lookup_place_neq.
    + rewrite lookup_place_eq; auto.
    + apply file_neq; simpl.
      apply third_file_neq.
      apply vert_check_edge_file; auto.
  - rewrite Forall_map.
    rewrite Forall_forall.
    intros ? _.
    unfold pre_lookup_black_king; simpl.
    rewrite lookup_place_neq.
    + rewrite lookup_place_eq; auto.
    + apply rank_neq; simpl.
      apply third_rank_neq.
      apply horiz_check_edge_rank; auto.
Qed.

Lemma W_oppose_pre_checkmates_correct3 :
  Forall pre_kings_unique W_oppose_pre_checkmates.
Proof.
  unfold W_oppose_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (opp_check cfg) eqn:Hchk.
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

Lemma dist_third_file f :
  edge_file f ->
  file_dist f (third_file f) = 2.
Proof.
  intros [|]; subst; auto.
Qed.

Lemma dist_third_rank r :
  edge_rank r ->
  rank_dist r (third_rank r) = 2.
Proof.
  intros [|]; subst; auto.
Qed.

Lemma W_oppose_pre_checkmates_correct4 :
  Forall pre_opp_to_play_not_in_check W_oppose_pre_checkmates.
Proof.
  unfold W_oppose_pre_checkmates.
  rewrite Forall_flat_map.
  rewrite Forall_forall.
  intros cfg Hcfg.
  destruct (opp_check cfg) eqn:Hchk.
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
    destruct pf2 as [_ pf2]; simpl in pf2.
    rewrite dist_third_file in pf2; [lia|].
    apply vert_check_edge_file; auto.
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
    destruct pf2 as [pf2 _]; simpl in pf2.
    rewrite dist_third_rank in pf2; [lia|].
    apply horiz_check_edge_rank; auto.
Qed.

Lemma NoDup_opp_cfg_rank cfg i :
  opp_check cfg = horiz ->
  In cfg oppose_configs ->
  In i (at_least_two_away (file (edge cfg))) ->
  NoDup
    [(file (edge cfg), third_file (rank (edge cfg)));
   edge cfg; (i, rank (edge cfg))].
Proof.
  intros pf1 pf2 pf3.
  repeat constructor.
  - intros [pf4|[pf4|[]]].
    + symmetry in pf4.
      apply f_equal with (f := rank) in pf4.
      simpl in pf4; symmetry in pf4.
      apply third_file_neq in pf4; auto.
      apply horiz_check_edge_rank; auto.
    + symmetry in pf4.
      apply f_equal with (f := rank) in pf4.
      simpl in pf4; symmetry in pf4.
      apply third_rank_neq in pf4; auto.
      apply horiz_check_edge_rank; auto.
  - intros [pf4|[]].
    apply f_equal with (f := file) in pf4.
    simpl in pf4.
    rewrite <- pf4 in pf3.
    apply In_at_least_two_away in pf3.
    rewrite fin_dist_refl in pf3.
    lia.
  - intros [].
Qed.

Lemma NoDup_opp_cfg_file cfg i :
  opp_check cfg = vert ->
  In cfg oppose_configs ->
  In i (at_least_two_away (rank (edge cfg))) ->
  NoDup
    [(third_file (file (edge cfg)), rank (edge cfg));
     edge cfg; (file (edge cfg), i)].
Proof.
  intros pf1 pf2 pf3.
  repeat constructor.
  - intros [pf4|[pf4|[]]].
    + symmetry in pf4.
      apply f_equal with (f := file) in pf4.
      simpl in pf4; symmetry in pf4.
      apply third_file_neq in pf4; auto.
      apply vert_check_edge_file; auto.
    + symmetry in pf4.
      apply f_equal with (f := file) in pf4.
      simpl in pf4; symmetry in pf4.
      apply third_file_neq in pf4; auto.
      apply vert_check_edge_file; auto.
  - intros [pf4|[]].
    apply f_equal with (f := rank) in pf4.
    simpl in pf4.
    rewrite <- pf4 in pf3.
    apply In_at_least_two_away in pf3.
    rewrite fin_dist_refl in pf3.
    lia.
  - intros [].
Qed.

Definition W_oppose_checkmates : list ChessState :=
  mk_ChessStates
    W_oppose_pre_checkmates
    W_oppose_pre_checkmates_correct1
    W_oppose_pre_checkmates_correct2
    W_oppose_pre_checkmates_correct3
    W_oppose_pre_checkmates_correct4.

Lemma dist_2_second_file f f' :
  edge_file f ->
  file_dist f f' = 1 ->
  f' = second_file f.
Proof.
  unfold second_file.
  intros [pf1|pf1] pf2.
  - destruct Dec.eq_dec; [|contradiction].
    rewrite pf1 in *.
    apply val_inj.
    simpl val at 2.
    unfold file_dist, fin_dist in pf2.
    rewrite Dist.dist_sym in pf2.
    rewrite StateAction.dist_sub in pf2.
    + simpl val at 2 in pf2; lia.
    + simpl val at 1; lia.
  - destruct Dec.eq_dec as [pf3|pf3].
    + rewrite pf1 in pf3; discriminate.
    + apply val_inj.
      simpl val at 2.
      unfold file_dist, fin_dist in pf2.
      rewrite pf1 in pf2.
      simpl val at 1 in pf2.
      rewrite StateAction.dist_sub in pf2.
      * lia.
      * pose proof (val_bound f'); lia.
Qed.

Lemma dist_2_second_rank r r' :
  edge_rank r ->
  rank_dist r r' = 1 ->
  r' = second_rank r.
Proof.
  unfold second_rank.
  intros [pf1|pf1] pf2.
  - destruct Dec.eq_dec; [|contradiction].
    rewrite pf1 in *.
    apply val_inj.
    simpl val at 2.
    unfold rank_dist, fin_dist in pf2.
    rewrite Dist.dist_sym in pf2.
    rewrite StateAction.dist_sub in pf2.
    + simpl val at 2 in pf2; lia.
    + simpl val at 1; lia.
  - destruct Dec.eq_dec as [pf3|pf3].
    + rewrite pf1 in pf3; discriminate.
    + apply val_inj.
      simpl val at 2.
      unfold rank_dist, fin_dist in pf2.
      rewrite pf1 in pf2.
      simpl val at 1 in pf2.
      rewrite StateAction.dist_sub in pf2.
      * lia.
      * pose proof (val_bound r'); lia.
Qed.

Lemma dist_third_file_1 f f' :
  edge_file f ->
  file_dist f f' = 1 ->
  file_dist (third_file f) f' = 1.
Proof.
  intros pf1 pf2.
  apply dist_2_second_file in pf2; auto.
  rewrite pf2.
  destruct pf1 as [pf1|pf1]; rewrite pf1; auto.
Qed.

Lemma dist_third_rank_1 r r' :
  edge_rank r ->
  rank_dist r r' = 1 ->
  rank_dist (third_rank r) r' = 1.
Proof.
  intros pf1 pf2.
  apply dist_2_second_rank in pf2; auto.
  rewrite pf2.
  destruct pf1 as [pf1|pf1]; rewrite pf1; auto.
Qed.

Lemma third_second_file_neq f :
  edge_file f ->
  third_file f <> second_file f.
Proof.
  intros.
  unfold third_file.
  unfold second_file.
  destruct Dec.eq_dec; discriminate.
Qed.

Lemma third_second_rank_neq r :
  edge_rank r ->
  third_rank r <> second_rank r.
Proof.
  intros.
  unfold third_rank.
  unfold second_rank.
  destruct Dec.eq_dec; discriminate.
Qed.

Lemma W_oppose_checkmates_correct : forall s,
  In s W_oppose_checkmates ->
  atomic_chess_res s = Some (Game.Win White).
Proof.
  intros s Hs.
  unfold atomic_chess_res.
  apply In_mk_ChessStates_weaken in Hs.
  unfold W_oppose_pre_checkmates in Hs.
  rewrite in_flat_map in Hs.
  destruct Hs as [cfg [pf1 pf2]].
  destruct (opp_check cfg) eqn:check_type.
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
        exists (file (edge cfg), i).
        exists Rook; split.
        -- rewrite s_board.
            apply lookup_piece_place_pieces.
           ++ rewrite s_play.
              right; right; left; auto.
           ++ apply NoDup_opp_cfg_file; auto.
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
           ++ apply third_file_neq in Hp1; auto.
              apply vert_check_edge_file; auto.
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
      destruct origin_dest_adj as [pf_r pf_f].
      rewrite Nat.le_1_r in pf_f.
      destruct pf_f as [f_0|f_1].
      * elim (no_resulting_check (dest m)).
        -- unfold updated_board.
           rewrite lookup_clear_neq; [|congruence].
           rewrite lookup_place_eq.
           congruence.
        -- exists (file (edge cfg), i), Rook; split.
           ++ unfold updated_board.
              rewrite lookup_clear_neq.
              ** rewrite lookup_place_neq.
                 --- rewrite s_board.
                     apply lookup_piece_place_pieces.
                     +++ right; right; now left.
                     +++ apply NoDup_opp_cfg_file; auto.
                 --- apply rank_neq; simpl.
                     intro Hi.
                     rewrite <- Hi in pf_r.
                     apply In_at_least_two_away in Hi2.
                     unfold rank_dist in pf_r; lia.
              ** rewrite pf2.
                 apply rank_neq; simpl.
                 intro Hi.
                 rewrite <- Hi in Hi2.
                 apply In_at_least_two_away in Hi2.
                 rewrite fin_dist_refl in Hi2; lia.
           ++ right; split.
              ** unfold vert_preadj.
                 apply fin_dist_0 in f_0; auto.
              ** intros p Hp1 Hp2.
                 apply ListUtil.not_Some_None; intros q Hq.
                 unfold updated_board in Hq.
                 rewrite s_board in Hq.
                 simpl in Hq.
                 lookup_piece_inversion; try discriminate.
                 --- apply not_rank_sbetween_right in Hp2; auto.
                 --- apply third_file_neq in Hp1; auto.
                     apply vert_check_edge_file; auto.
                 --- congruence.
                 --- apply not_rank_sbetween_left in Hp2; auto.
      * elim (no_resulting_check (dest m)).
        -- unfold updated_board.
           rewrite lookup_clear_neq; [|congruence].
           rewrite lookup_place_eq.
           congruence.
        -- exists (third_file (file (edge cfg)),
            rank (edge cfg)), King; split.
           ++ unfold updated_board.
              rewrite lookup_clear_neq.
              ** rewrite lookup_place_neq.
                 --- rewrite s_board.
                     apply lookup_piece_place_pieces.
                     +++ now left.
                     +++ apply NoDup_opp_cfg_file; auto.
                 --- apply file_neq; simpl.
                     apply dist_2_second_file in f_1;
                       [|apply vert_check_edge_file; auto].
                     rewrite f_1.
                     apply third_second_file_neq.
                     apply vert_check_edge_file; auto.
              ** rewrite pf2.
                 apply file_neq.
                 apply not_eq_sym.
                 apply third_file_neq.
                 apply vert_check_edge_file; auto.
           ++ split.
              ** auto.
              ** simpl.
                 rewrite dist_third_file_1; auto.
                 apply vert_check_edge_file; auto.
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
        exists (i, rank (edge cfg)).
        exists Rook; split.
        -- rewrite s_board.
            apply lookup_piece_place_pieces.
           ++ rewrite s_play.
              right; right; left; auto.
           ++ apply NoDup_opp_cfg_rank; auto.
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
           ++ apply third_rank_neq in Hp1; auto.
              apply horiz_check_edge_rank; auto.
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
      destruct origin_dest_adj as [pf_r pf_f].
      rewrite Nat.le_1_r in pf_r.
      destruct pf_r as [r_0|r_1].
      * elim (no_resulting_check (dest m)).
        -- unfold updated_board.
           rewrite lookup_clear_neq; [|congruence].
           rewrite lookup_place_eq.
           congruence.
        -- exists (i, rank (edge cfg)), Rook; split.
           ++ unfold updated_board.
              rewrite lookup_clear_neq.
              ** rewrite lookup_place_neq.
                 --- rewrite s_board.
                     apply lookup_piece_place_pieces.
                     +++ right; right; now left.
                     +++ apply NoDup_opp_cfg_rank; auto.
                 --- apply file_neq; simpl.
                     intro Hi.
                     rewrite <- Hi in pf_f.
                     apply In_at_least_two_away in Hi2.
                     unfold file_dist in pf_f; lia.
              ** rewrite pf2.
                 apply file_neq; simpl.
                 intro Hi.
                 rewrite <- Hi in Hi2.
                 apply In_at_least_two_away in Hi2.
                 rewrite fin_dist_refl in Hi2; lia.
           ++ left; split.
              ** unfold horiz_preadj.
                 apply fin_dist_0 in r_0; auto.
              ** intros p Hp1 Hp2.
                 apply ListUtil.not_Some_None; intros q Hq.
                 unfold updated_board in Hq.
                 rewrite s_board in Hq.
                 simpl in Hq.
                 lookup_piece_inversion; try discriminate.
                 --- apply not_file_sbetween_right in Hp2; auto.
                 --- apply third_rank_neq in Hp1; auto.
                     apply horiz_check_edge_rank; auto.
                 --- congruence.
                 --- apply not_file_sbetween_left in Hp2; auto.
      * elim (no_resulting_check (dest m)).
        -- unfold updated_board.
           rewrite lookup_clear_neq; [|congruence].
           rewrite lookup_place_eq.
           congruence.
        -- exists (file (edge cfg),
           third_rank (rank (edge cfg))), King; split.
           ++ unfold updated_board.
              rewrite lookup_clear_neq.
              ** rewrite lookup_place_neq.
                 --- rewrite s_board.
                     apply lookup_piece_place_pieces.
                     +++ now left.
                     +++ apply NoDup_opp_cfg_rank; auto.
                 --- apply rank_neq; simpl.
                     apply dist_2_second_rank in r_1;
                       [|apply horiz_check_edge_rank; auto].
                     rewrite r_1.
                     apply third_second_rank_neq.
                     apply horiz_check_edge_rank; auto.
              ** rewrite pf2.
                 apply rank_neq.
                 apply not_eq_sym.
                 apply third_rank_neq.
                 apply horiz_check_edge_rank; auto.
           ++ split.
              ** simpl.
                 rewrite dist_third_rank_1; auto.
                 apply horiz_check_edge_rank; auto.
              ** auto.
Qed.

Lemma W_oppose_checkmates_mat :
  Forall (material_eq KRvK) W_oppose_checkmates.
Proof.
  rewrite Forall_forall.
  intros s Hs.
  apply In_mk_ChessStates_weaken in Hs.
  unfold W_oppose_pre_checkmates in Hs.
  rewrite in_flat_map in Hs.
  destruct Hs as [cfg [pf1 pf2]].
  destruct (opp_check cfg) eqn:?.
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    unfold material_eq.
    rewrite <- PreChessState_of_ChessState_pre_board.
    rewrite <- Hi1.
    unfold pre_board.
    intros.
    rewrite count_place_pieces.
    + destruct c; destruct p; reflexivity.
    + apply NoDup_opp_cfg_file; auto.
  - rewrite in_map_iff in pf2.
    destruct pf2 as [i [Hi1 Hi2]].
    unfold material_eq.
    rewrite <- PreChessState_of_ChessState_pre_board.
    rewrite <- Hi1.
    unfold pre_board.
    intros.
    rewrite count_place_pieces.
    + destruct c; destruct p; reflexivity.
    + apply NoDup_opp_cfg_rank; auto.
Qed.

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

Lemma PreChessState_ext : forall s s',
  pre_chess_to_play s = pre_chess_to_play s' ->
  pre_board s = pre_board s' ->
  pre_white_king s = pre_white_king s' ->
  pre_black_king s = pre_black_king s' ->
  s = s'.
Proof.
  intros.
  destruct s, s'; simpl in *.
  congruence.
Qed.

Lemma horiz_checkmate_edge_rank : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  horiz_adj (board s) pos (black_king s) ->
  edge_rank (rank (black_king s)).
Proof.
Admitted.

Lemma vert_checkmate_edge_file : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  vert_adj (board s) pos (black_king s) ->
  edge_file (file (black_king s)).
Proof.
Admitted.

Lemma horiz_checkmate_third_rank : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  horiz_adj (board s) pos (black_king s) ->
  rank (white_king s) = third_rank (rank (black_king s)).
Proof.
Admitted.

Lemma vert_checkmate_third_file : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  vert_adj (board s) pos (black_king s) ->
  file (white_king s) = third_file (file (black_king s)).
Proof.
Admitted.

Lemma horiz_checkmate_opp_or_second_file : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  horiz_adj (board s) pos (black_king s) ->
  file (white_king s) = file (black_king s) \/
  (edge_file (file (black_king s)) /\ file (white_king s) = second_file (file (black_king s))).
Proof.
Admitted.

Lemma vert_checkmate_opp_or_second_rank : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  vert_adj (board s) pos (black_king s) ->
  rank (white_king s) = rank (black_king s) \/
  (edge_rank (rank (black_king s)) /\ rank (white_king s) = second_rank (rank (black_king s))).
Proof.
Admitted.

Lemma horiz_checkmate_rook_distant : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  horiz_adj (board s) pos (black_king s) ->
  2 <= fin_dist (file (black_king s)) (file pos).
Proof.
Admitted.

Lemma vert_checkmate_rook_distant : forall s pos,
  material_eq KRvK s ->
  chess_to_play s = Black ->
  enum_chess_moves s = [] ->
  lookup_piece pos (board s) = Some (White, Rook) ->
  vert_adj (board s) pos (black_king s) ->
  2 <= fin_dist (rank (black_king s)) (rank pos).
Proof.
Admitted.

Lemma pre_board_reduce :
  forall p b wk bk,
  pre_board {|
    pre_chess_to_play := p;
    pre_board := b;
    pre_white_king := wk;
    pre_black_king := bk;
  |} = b.
Proof.
  reflexivity.
Qed.

Lemma lookup_piece_place_piece_Some_inv 
  pl pc pos pl' pc' pos' b :
  lookup_piece pos (place_piece pl' pc' pos' b) = Some (pl, pc) ->
  (pl, pc, pos) = (pl', pc', pos') \/
  lookup_piece pos b = Some (pl, pc).
Proof.
  intro pf.
  destruct (Dec.eq_dec pos pos').
  - subst; left.
    rewrite lookup_place_eq in pf.
    congruence.
  - rewrite lookup_place_neq in pf; auto.
Qed.

Lemma lookup_piece_Some_In ps pos pl pc :
  lookup_piece pos (place_pieces ps) = Some (pl, pc) ->
  In (pl, pc, pos) ps.
Proof.
  induction ps as [|[[pl' pc'] pos']]; intro pf.
  - simpl in pf.
    rewrite lookup_piece_empty in pf.
    discriminate.
  - simpl in pf.
    apply lookup_piece_place_piece_Some_inv in pf.
    destruct pf.
    + left; auto.
    + right; apply IHps; auto.
Qed.

Lemma list_count_filter {X} `{Dec.Discrete X}
  (x : X) (l : list X) :
  list_count x l =
  List.length (filter (fun x' =>
    if Dec.eq_dec x x' then true else false) l).
Proof.
  induction l as [|y l'].
  - reflexivity.
  - simpl.
    destruct Dec.eq_dec; simpl; congruence.
Qed.

Lemma filter_map {X Y} (f : X -> Y) (p : Y -> bool) (xs : list X) :
  filter p (map f xs) =
  map f (filter (fun x => p (f x)) xs).
Proof.
  induction xs.
  - reflexivity.
  - simpl.
    destruct p; simpl; congruence.
Qed.

Lemma length_lt {X} (xs : list X) : forall ys,
  NoDup xs ->
  (forall x, In x xs -> In x ys) ->
  forall x, ~ In x xs -> In x ys ->
  length xs < length ys.
Proof.
  induction xs as [|x' xs']; intros ys nd_xs pf_inc x x_xs x_ys.
  - destruct ys.
    + destruct x_ys.
    + simpl; lia.
  - simpl.
    assert (In x' ys) as x'_ys by
      (apply pf_inc; now left).
    destruct (in_split _ _ x'_ys) as [l1 [l2 pf]].
    rewrite pf.
    rewrite app_length; simpl.
    rewrite Nat.add_succ_r.
    rewrite <- app_length.
    rewrite <- Nat.succ_lt_mono.
    apply IHxs' with (x := x).
    + now inversion nd_xs.
    + intros y Hy.
      specialize (pf_inc y (or_intror Hy)).
      rewrite pf in pf_inc.
      apply in_or_app.
      apply in_app_or in pf_inc.
      destruct pf_inc as [|[pf_eq|]]; auto.
      inversion nd_xs.
      elim H1; congruence.
    + intro; apply x_xs; now right.
    + rewrite pf in x_ys.
      apply in_or_app.
      apply in_app_or in x_ys.
      destruct x_ys as [|[pf_eq|]]; auto.
      elim x_xs; now left.
Qed.

Lemma NoDup_map_inj_on {X Y} (f : X -> Y) :
  forall (xs : list X),
  (forall x x' : X, In x xs -> In x' xs -> f x = f x' -> x = x') ->
  NoDup xs -> NoDup (map f xs).
Proof.
  induction xs as [|x ys]; intros Hf nd_xs.
  - constructor.
  - simpl; constructor.
    + intro pf.
      rewrite in_map_iff in pf.
      destruct pf as [y [Hy1 Hy2]].
      inversion nd_xs.
      apply H1.
      apply Hf in Hy1.
      * congruence.
      * now right.
      * now left.
    + apply IHys.
      * intros; apply Hf; auto.
        -- now right.
        -- now right.
      * now inversion nd_xs.
Qed.

Lemma list_count_count_le ps b :
  (forall pl pc p, In (pl, pc, p) ps ->
    lookup_piece p b = Some (pl, pc)) ->
  NoDup (map snd ps) ->
  forall pl pc p,
    ~ In (pl, pc, p) ps ->
    lookup_piece p b = Some (pl, pc) ->
    list_count (pl, pc) (map fst ps) < count pl pc b.
Proof.
  intros ps_b nd_ps pl pc pos pos_ps pos_b.
  rewrite <- MaterialPositions.mp_of_board_count.
  rewrite list_count_filter.
  rewrite filter_map.
  rewrite map_length.
  rewrite <- map_length with (f := snd).
  apply length_lt with (x := pos).
  - apply NoDup_map_inj_on.
    + intros.
      rewrite filter_In in *.
      destruct H as [_ pf1].
      destruct H0 as [_ pf2].
      destruct Dec.eq_dec; try discriminate.
      destruct Dec.eq_dec; try discriminate.
      destruct x, x'.
      rewrite pair_equal_spec; split;
        simpl in *; congruence.
    + apply NoDup_filter.
      apply NoDup_map_inv in nd_ps; auto.
  - intros p pf.
    apply MaterialPositions.mp_of_board_correct1.
    unfold lookup_piece in pos_b.
    rewrite in_map_iff in pf.
    destruct pf as [[p' pos'] [pf1 pf2]].
    rewrite filter_In in pf2.
    destruct pf2 as [pf2 pf3].
    destruct Dec.eq_dec; try discriminate.
    apply ps_b; simpl in *; congruence.
  - intro pf.
    apply pos_ps.
    rewrite in_map_iff in pf.
    destruct pf as [[] [pf1 pf2]].
    rewrite filter_In in pf2.
    destruct pf2 as [pf2 pf3].
    destruct Dec.eq_dec; try discriminate.
    simpl in *; congruence.

  - apply MaterialPositions.mp_of_board_correct1; auto.
Qed.

Lemma place_pieces_eq b ps :
  (forall pl pc p, In (pl, pc, p) ps ->
    lookup_piece p b = Some (pl, pc)) ->
  (forall pl pc,
    count pl pc b = list_count (pl, pc) (map fst ps)) ->
  NoDup (map snd ps) ->
  place_pieces ps = b.
Proof.
  intros pf1 pf2 pf3.
  apply Mat.mat_ext.
  intros pos.
  fold @lookup_piece.
  destruct (lookup_piece pos (place_pieces ps))
    as [[pl pc]|] eqn:Hps.
  - symmetry; apply pf1.
    apply lookup_piece_Some_In; auto.
  - destruct (lookup_piece pos b) 
      as [[pl pc]|] eqn:Hb; auto.
    specialize (pf2 pl pc).
    assert (list_count (pl, pc) (map fst ps) <
      count pl pc b); [|lia].
    apply list_count_count_le with (p := pos); auto.
    intro pf.
    apply lookup_piece_place_pieces_Some in pf.
    destruct pf; congruence.
Qed.

Lemma pos_eta (p : Pos) :
  p = (file p, rank p).
Proof.
  now destruct p.
Qed.

Ltac destruct_nd :=
  match goal with
  | [ |- NoDup _ ] => constructor; destruct_nd
  | _ => idtac
  end.

Lemma W_checkmates_correct2 : forall s,
  atomic_chess_res s = Some (Game.Win White) ->
  material_eq KRvK s ->
  In s W_checkmates.
Proof.
  intros s pf1 pf2.
  unfold atomic_chess_res in pf1.
  destruct Dec.dec as [chk|];
  [|destruct enum_chess_moves; discriminate].
  destruct enum_chess_moves eqn:moves; [|discriminate].
  inversion pf1 as [s_play]; clear pf1.
  rewrite <- (opp_invol White) in s_play.
  apply opp_inj in s_play.
  unfold in_check in chk.
  rewrite s_play in chk.
  specialize (chk (black_king s) (lookup_black_king s)).
  unfold is_threatened_by in chk.
  destruct chk as [pos' [piece [pf3 pf4]]].
  pose proof (mat := pf2).
  unfold material_eq in pf2.
  specialize (pf2 White piece).
  rewrite <- MaterialPositions.mp_of_board_count in pf2.
  pose proof (pf5 := pf3).
  apply MaterialPositions.mp_of_board_correct1 in pf5.
  destruct MaterialPositions.mp_of_board; [destruct pf5|].
  clear pf5.
  destruct piece; try discriminate; clear pf2.
  - apply kings_unique in pf3.
    rewrite pf3 in pf4.
    apply neighbor_preadj_kings in pf4.
    destruct pf4.
  - unfold W_checkmates.
    simpl in pf3, s_play.
    apply in_or_app.
    destruct pf4 as [h_chk|v_chk].
    + destruct (horiz_checkmate_opp_or_second_file s pos') as [opp|[corner1 corner2]]; auto.
      * right; apply In_mk_ChessStates_strengthen.
        unfold W_oppose_pre_checkmates.
        rewrite in_flat_map.
        assert (edge_rank (rank (black_king s))) as r_e by
            (eapply horiz_checkmate_edge_rank; eauto).
        exists {|
          edge := black_king s;
          opp_check := horiz
        |}; split.
        -- apply in_or_app; right.
           apply in_or_app; right.
           destruct r_e as [r_e1|r_e8].
           ++ apply in_or_app; left.
              rewrite in_map_iff.
              exists (file (black_king s)).
              split; [|apply all_fin_In].
              rewrite <- r_e1.
              now destruct (black_king s).
           ++ apply in_or_app; right.
              rewrite in_map_iff.
              exists (file (black_king s)).
              split; [|apply all_fin_In].
              rewrite <- r_e8.
              now destruct (black_king s).
        -- simpl opp_check; rewrite in_map_iff.
           exists (file pos'); split.
           ++ apply PreChessState_ext.
              ** simpl; congruence.
              ** rewrite pre_board_reduce.
                 simpl edge.
                 --- simpl pre_board.
                     apply place_pieces_eq.
                     +++ simpl; intros pl pc pos pf.
                         destruct_or; inversion pf; subst.
                         *** rewrite <- opp.
                             erewrite <- horiz_checkmate_third_rank; eauto.
                             rewrite <- (lookup_white_king s).
                             now destruct (white_king s).
                         *** apply s.
                         *** rewrite <- pf3.
                             unfold horiz_adj in h_chk.
                             unfold horiz_preadj in h_chk.
                             destruct h_chk as [h_chk _].
                             rewrite <- h_chk.
                             now destruct pos'.
                     +++ unfold material_eq in mat.
                         intros; rewrite mat.
                         destruct pl, pc; reflexivity.
                     +++ simpl; destruct_nd; try intros [|].
                         *** apply (f_equal rank) in H; simpl in H.
                             apply third_rank_neq in H; auto.
                         *** destruct H as [|[]].
                             apply (f_equal rank) in H; simpl in H.
                             apply third_rank_neq in H; auto.
                         *** destruct h_chk as [h_chk _].
                             unfold horiz_preadj in h_chk.
                             rewrite <- h_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_black_king in pf3.
                             congruence.
                         *** destruct H.
                         *** intros [].
              ** simpl.
                 rewrite <- opp.
                 rewrite <- horiz_checkmate_third_rank with (pos := pos'); auto.
                 now destruct (white_king s).
              ** reflexivity.
           ++ apply (@at_least_two_away_In 8).
              apply horiz_checkmate_rook_distant; auto.
      * left; apply In_mk_ChessStates_strengthen.
        unfold W_corner_pre_checkmates.
        rewrite in_flat_map.
        exists {|
          corner := black_king s;
          off_corner := white_king s;
          check := horiz
        |}; split.
        -- unfold corner_king_configs.
           assert (edge_rank (rank (black_king s))) as corner3 by
             (eapply horiz_checkmate_edge_rank; eauto).
           assert (rank (white_king s) = third_rank (rank (black_king s))) as pf4 by
             (eapply horiz_checkmate_third_rank; eauto).
           rewrite (pos_eta (black_king s)).
           rewrite (pos_eta (white_king s)).
           rewrite pf4.
           rewrite corner2.
           destruct corner1 as [c1|c1]; rewrite c1;
           destruct corner3 as [c3|c3]; rewrite c3.
           ++ left; reflexivity.
           ++ right; right; left; reflexivity.
           ++ right; right; right; right; left; reflexivity.
           ++ right; right; right; right; right; right; left; reflexivity.
        -- simpl check; rewrite in_map_iff.
           exists (file pos'); split.
           ++ apply PreChessState_ext.
              ** simpl; congruence.
              ** rewrite pre_board_reduce.
                 simpl edge.
                 --- simpl pre_board.
                     apply place_pieces_eq.
                     +++ simpl; intros pl pc pos pf.
                         destruct_or; inversion pf; subst.
                         *** apply s.
                         *** apply s.
                         *** unfold horiz_adj in h_chk.
                             destruct h_chk as [h_chk _].
                             unfold horiz_preadj in h_chk.
                             rewrite <- h_chk.
                             rewrite <- pos_eta; auto.
                     +++ unfold material_eq in mat.
                         intros; rewrite mat.
                         destruct pl, pc; reflexivity.
                     +++ simpl; destruct_nd; try intros [|].
                         *** apply (f_equal (fun p =>
                               lookup_piece p (board s))) in H.
                             rewrite lookup_black_king in H.
                             rewrite lookup_white_king in H.
                             congruence.
                         *** destruct H as [|[]].
                             destruct h_chk as [h_chk _].
                             unfold horiz_preadj in h_chk.
                             rewrite <- h_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_white_king in pf3.
                             congruence.
                         *** destruct h_chk as [h_chk _].
                             unfold horiz_preadj in h_chk.
                             rewrite <- h_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_black_king in pf3.
                             congruence.
                         *** destruct H.
                         *** intros [].
              ** reflexivity.
              ** reflexivity.
           ++ apply (@at_least_two_away_In 8).
              apply horiz_checkmate_rook_distant; auto.
    + destruct (vert_checkmate_opp_or_second_rank s pos') as [opp|[corner1 corner2]]; auto.
      * right; apply In_mk_ChessStates_strengthen.
        unfold W_oppose_pre_checkmates.
        rewrite in_flat_map.
        assert (edge_file (file (black_king s))) as f_e by
            (eapply vert_checkmate_edge_file; eauto).
        exists {|
          edge := black_king s;
          opp_check := vert
        |}; split.
        -- destruct f_e as [f_ea|f_eh].
           ++ apply in_or_app; left.
              rewrite in_map_iff.
              exists (rank (black_king s)).
              split; [|apply all_fin_In].
              rewrite <- f_ea.
              now destruct (black_king s).
           ++ apply in_or_app; right.
              apply in_or_app; left.
              rewrite in_map_iff.
              exists (rank (black_king s)).
              split; [|apply all_fin_In].
              rewrite <- f_eh.
              now destruct (black_king s).
        -- simpl opp_check; rewrite in_map_iff.
           exists (rank pos'); split.
           ++ apply PreChessState_ext.
              ** simpl; congruence.
              ** rewrite pre_board_reduce.
                 simpl edge.
                 --- simpl pre_board.
                     apply place_pieces_eq.
                     +++ simpl; intros pl pc pos pf.
                         destruct_or; inversion pf; subst.
                         *** rewrite <- opp.
                             erewrite <- vert_checkmate_third_file; eauto.
                             rewrite <- (lookup_white_king s).
                             now destruct (white_king s).
                         *** apply s.
                         *** rewrite <- pf3.
                             unfold vert_adj in v_chk.
                             unfold vert_preadj in v_chk.
                             destruct v_chk as [v_chk _].
                             rewrite <- v_chk.
                             now destruct pos'.
                     +++ unfold material_eq in mat.
                         intros; rewrite mat.
                         destruct pl, pc; reflexivity.
                     +++ simpl; destruct_nd; try intros [|].
                         *** apply (f_equal file) in H; simpl in H.
                             apply third_file_neq in H; auto.
                         *** destruct H as [|[]].
                             apply (f_equal file) in H; simpl in H.
                             apply third_file_neq in H; auto.
                         *** destruct v_chk as [v_chk _].
                             unfold vert_preadj in v_chk.
                             rewrite <- v_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_black_king in pf3.
                             congruence.
                         *** destruct H.
                         *** intros [].
              ** simpl.
                 rewrite <- opp.
                 rewrite <- vert_checkmate_third_file with (pos := pos'); auto.
                 now destruct (white_king s).
              ** reflexivity.
           ++ apply (@at_least_two_away_In 8).
              apply vert_checkmate_rook_distant; auto.
      * left; apply In_mk_ChessStates_strengthen.
        unfold W_corner_pre_checkmates.
        rewrite in_flat_map.
        exists {|
          corner := black_king s;
          off_corner := white_king s;
          check := vert
        |}; split.
        -- unfold corner_king_configs.
           assert (edge_file (file (black_king s))) as corner3 by
             (eapply vert_checkmate_edge_file; eauto).
           assert (file (white_king s) = third_file (file (black_king s))) as pf4 by
             (eapply vert_checkmate_third_file; eauto).
           rewrite (pos_eta (black_king s)).
           rewrite (pos_eta (white_king s)).
           rewrite pf4.
           rewrite corner2.
           destruct corner1 as [c1|c1]; rewrite c1;
           destruct corner3 as [c3|c3]; rewrite c3.
           ++ right; left; reflexivity.
           ++ right; right; right; right; right; left; reflexivity.
           ++ right; right; right; left; reflexivity.
           ++ right; right; right; right; right; right; right; left; reflexivity.
        -- simpl check; rewrite in_map_iff.
           exists (rank pos'); split.
           ++ apply PreChessState_ext.
              ** simpl; congruence.
              ** rewrite pre_board_reduce.
                 simpl edge.
                 --- simpl pre_board.
                     apply place_pieces_eq.
                     +++ simpl; intros pl pc pos pf.
                         destruct_or; inversion pf; subst.
                         *** apply s.
                         *** apply s.
                         *** unfold vert_adj in v_chk.
                             destruct v_chk as [v_chk _].
                             unfold vert_preadj in v_chk.
                             rewrite <- v_chk.
                             rewrite <- pos_eta; auto.
                     +++ unfold material_eq in mat.
                         intros; rewrite mat.
                         destruct pl, pc; reflexivity.
                     +++ simpl; destruct_nd; try intros [|].
                         *** apply (f_equal (fun p =>
                               lookup_piece p (board s))) in H.
                             rewrite lookup_black_king in H.
                             rewrite lookup_white_king in H.
                             congruence.
                         *** destruct H as [|[]].
                             destruct v_chk as [v_chk _].
                             unfold vert_preadj in v_chk.
                             rewrite <- v_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_white_king in pf3.
                             congruence.
                         *** destruct v_chk as [v_chk _].
                             unfold vert_preadj in v_chk.
                             rewrite <- v_chk in H.
                             rewrite <- pos_eta in H.
                             rewrite H in pf3.
                             rewrite lookup_black_king in pf3.
                             congruence.
                         *** destruct H.
                         *** intros [].
              ** reflexivity.
              ** reflexivity.
           ++ apply (@at_least_two_away_In 8).
              apply vert_checkmate_rook_distant; auto.
Qed.

Lemma W_checkmates_correct3 :
  Forall (material_eq KRvK) W_checkmates.
Proof.
  apply Forall_app; split.
  - apply W_corner_checkmates_mat.
  - apply W_oppose_checkmates_mat.
Qed.
