Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Chess.Chess.
Require Import TBGen.StratSymTB.TB.
Require Import Chess.TB.Material.KRvK. (*pre stuff*)

Definition emptyb (b : Board) (p : Pos) :=
  match lookup_piece p b with
  | Some _ => false
  | None => true
  end.

Definition captures pl : list (option (Player.Player * Piece)) :=
  [ Some (pl, Queen);
    Some (pl, Rook);
    Some (pl, Bishop);
    Some (pl, Knight);
    None
  ].

Definition reverse_prestates (s : ChessState) : list PreChessState.
Proof.
  pose (pl := Player.opp (chess_to_play s)).
  refine (filter (fun s => negb (is_threatened_byb
    (pre_board s)
    (pre_king s (Player.opp (pre_chess_to_play s)))
    (pre_chess_to_play s))) _).
  pose (dests := list_player_pieces (board s) pl).
  refine (flat_map _ dests).
  intros [p_dest pc].
  pose (cand_origs :=
    filter (emptyb (board s))
    (candidate_destinations pc s p_dest)).
  refine (flat_map _ cand_origs).
  intro p_orig.
  refine (map _ (captures (chess_to_play s))).
  intro o.
  refine {|
    pre_chess_to_play := pl;
    pre_board := _;
    pre_white_king :=
      match chess_to_play s with
      | Player.White => white_king s
      | Player.Black =>
        match pc with
        | King => p_orig
        | _ => white_king s
        end
      end;
    pre_black_king :=
      match chess_to_play s with
      | Player.White =>
        match pc with
        | King => p_orig
        | _ => black_king s
        end
      | Player.Black => black_king s
      end
  |}.
  exact (place_piece pl pc p_orig (Mat.mupdate p_dest o (board s))).
Defined.

Lemma reverse_prestates_correct1 s :
  Forall pre_lookup_white_king (reverse_prestates s).
Proof.
  unfold reverse_prestates.
  rewrite Forall_forall.
  intros s' pf.
  rewrite filter_In in pf.
  destruct pf as [pf no_chk].
  rewrite in_flat_map in pf.
  destruct pf as [[p pc] [Hp pf]].
  rewrite in_flat_map in pf.
  destruct pf as [p' [Hp' pf]].
  rewrite in_map_iff in pf.
  destruct pf as [o [pf pf']].
  unfold pre_lookup_white_king.
  rewrite <- pf; simpl.
  destruct (chess_to_play s) eqn:s_play.
  - unfold lookup_piece, place_piece, clear.
    rewrite Mat.maccess_mupdate_neq.
    + rewrite Mat.maccess_mupdate_neq.
      * apply s.
      * rewrite list_player_pieces_correct in Hp.
        intros ?; subst.
        rewrite lookup_white_king in Hp; discriminate.
    + rewrite filter_In in Hp'.
      destruct Hp' as [_ Hp'].
      unfold emptyb in Hp'.
      intros ?; subst.
      rewrite lookup_white_king in Hp'; discriminate.
  - assert (forall (X : Type) (x x' : X),
      match pc with
      | King => x
      | _ => x'
      end =
      match Games.Util.Dec.eq_dec pc King with
      | left _ => x
      | right _ => x'
      end) as Hmatch.
    { intros.
      destruct (Games.Util.Dec.eq_dec pc King).
      + subst; reflexivity.
      + destruct pc; try reflexivity.
        contradiction.
    }
    rewrite Hmatch; clear Hmatch.
    destruct Games.Util.Dec.eq_dec.
    + subst; apply Mat.maccess_mupdate_eq.
    + unfold lookup_piece, place_piece.
      rewrite Mat.maccess_mupdate_neq.
      * rewrite Mat.maccess_mupdate_neq.
        -- apply s.
        -- intros ?; subst.
           rewrite list_player_pieces_correct in Hp.
           rewrite lookup_white_king in Hp.
           congruence.
      * intros ?; subst.
        rewrite filter_In in Hp'.
        destruct Hp' as [_ Hp'].
        unfold emptyb in Hp'.
        rewrite lookup_white_king in Hp'.
        discriminate.
Qed.

Lemma reverse_prestates_correct2 s :
  Forall pre_lookup_black_king (reverse_prestates s).
Proof.
  unfold reverse_prestates.
  rewrite Forall_forall.
  intros s' pf.
  rewrite filter_In in pf.
  destruct pf as [pf no_chk].
  rewrite in_flat_map in pf.
  destruct pf as [[p pc] [Hp pf]].
  rewrite in_flat_map in pf.
  destruct pf as [p' [Hp' pf]].
  rewrite in_map_iff in pf.
  destruct pf as [o [pf pf']].
  unfold pre_lookup_black_king.
  rewrite <- pf; simpl.
  destruct (chess_to_play s) eqn:s_play.
  - assert (forall (X : Type) (x x' : X),
      match pc with
      | King => x
      | _ => x'
      end =
      match Games.Util.Dec.eq_dec pc King with
      | left _ => x
      | right _ => x'
      end) as Hmatch.
    { intros.
      destruct (Games.Util.Dec.eq_dec pc King).
      + subst; reflexivity.
      + destruct pc; try reflexivity.
        contradiction.
    }
    rewrite Hmatch; clear Hmatch.
    destruct Games.Util.Dec.eq_dec.
    + subst; apply Mat.maccess_mupdate_eq.
    + unfold lookup_piece, place_piece.
      rewrite Mat.maccess_mupdate_neq.
      * rewrite Mat.maccess_mupdate_neq.
        -- apply s.
        -- intros ?; subst.
           rewrite list_player_pieces_correct in Hp.
           rewrite lookup_black_king in Hp.
           congruence.
      * intros ?; subst.
        rewrite filter_In in Hp'.
        destruct Hp' as [_ Hp'].
        unfold emptyb in Hp'.
        rewrite lookup_black_king in Hp'.
        discriminate.
  - unfold lookup_piece, place_piece, clear.
    rewrite Mat.maccess_mupdate_neq.
    + rewrite Mat.maccess_mupdate_neq.
      * apply s.
      * rewrite list_player_pieces_correct in Hp.
        intros ?; subst.
        rewrite lookup_black_king in Hp; discriminate.
    + rewrite filter_In in Hp'.
      destruct Hp' as [_ Hp'].
      unfold emptyb in Hp'.
      intros ?; subst.
      rewrite lookup_black_king in Hp'; discriminate.
Qed.

Lemma King_not_in_captures : forall p p',
  ~ In (Some (p, King)) (captures p').
Proof.
  intros p p' pf.
  simpl in pf.
  destruct_or; congruence.
Qed.

Lemma reverse_prestates_correct3 s :
  Forall pre_kings_unique (reverse_prestates s).
Proof.
  rewrite Forall_forall.
  intros s' Hs' p pos Hpos.
  unfold reverse_prestates in Hs'.
  rewrite filter_In in Hs'.
  rewrite in_flat_map in Hs'.
  destruct Hs' as [[[pos1 pc] [pf1 pf2]]].
  rewrite in_flat_map in pf2.
  destruct pf2 as [pos2 [pf2 pf3]].
  rewrite in_map_iff in pf3.
  destruct pf3 as [o [Ho1 Ho2]].
  rewrite <- Ho1 in *; simpl in Hpos.
  lookup_piece_inversion; subst.
  - inversion Hpos; subst.
    destruct (chess_to_play s) eqn:s_play; simpl; auto.
  - destruct (Games.Util.Dec.eq_dec pos pos1).
    + subst.
      unfold lookup_piece in Hpos.
      rewrite Mat.maccess_mupdate_eq in Hpos.
      rewrite Hpos in Ho2.
      apply King_not_in_captures in Ho2; destruct Ho2.
    + unfold lookup_piece in Hpos.
      rewrite Mat.maccess_mupdate_neq in Hpos; auto.
      apply s in Hpos.
      rewrite Hpos.
      destruct p; simpl.
      * destruct (chess_to_play s) eqn:s_play; auto.
        destruct pc; auto.
        simpl in H.
        elim n.
        rewrite Hpos; symmetry.
        apply s.
        rewrite list_player_pieces_correct in pf1; auto.
      * destruct (chess_to_play s) eqn:s_play; auto.
        destruct pc; auto.
        simpl in H.
        elim n.
        rewrite Hpos; symmetry.
        apply s.
        rewrite list_player_pieces_correct in pf1; auto.
Qed.

Lemma reverse_prestates_correct4 s :
  Forall pre_opp_to_play_not_in_check (reverse_prestates s).
Proof.
  rewrite Forall_forall.
  intros s' pf.
  pose proof (pf' := pf).
  unfold reverse_prestates in pf.
  rewrite filter_In in pf.
  destruct pf as [_ pf].
  unfold pre_opp_to_play_not_in_check.
  unfold is_threatened_byb in pf.
  destruct Games.Util.Dec.dec; [discriminate|].
  intros p Hp.
  pose proof (reverse_prestates_correct3 s) as Hs.
  rewrite Forall_forall in Hs.
  apply (Hs s' pf') in Hp; congruence.
Qed.

Global Instance Vec_Disc {X} `{Games.Util.Dec.Discrete X} {n} :
  Games.Util.Dec.Discrete (Vec.Vec X n).
Proof.
  constructor.
  induction n.
  - intros [] []; now left.
  - intros [x v] [x' v'].
    destruct (Games.Util.Dec.eq_dec x x');
      [subst|right; intro pf; inversion pf; contradiction].
    destruct (IHn v v');
      [subst|right; intro pf; inversion pf; contradiction].
    now left.
Defined.

Definition reverse_states (s : ChessState) : list ChessState :=
  mk_ChessStates
    (reverse_prestates s)
    (reverse_prestates_correct1 s)
    (reverse_prestates_correct2 s)
    (reverse_prestates_correct3 s)
    (reverse_prestates_correct4 s).

Global Instance : Games.Util.Dec.Discrete PreChessState.
Proof.
  constructor.
  intros [p1 b1 wk1 bk1] [p2 b2 wk2 bk2].
  destruct (Games.Util.Dec.eq_dec p1 p2);
    [|right; intro pf; inversion pf; contradiction].
  destruct (Games.Util.Dec.eq_dec b1 b2);
    [|right; intro pf; inversion pf; contradiction].
  destruct (Games.Util.Dec.eq_dec wk1 wk2);
    [|right; intro pf; inversion pf; contradiction].
  destruct (Games.Util.Dec.eq_dec bk1 bk2);
    [|right; intro pf; inversion pf; contradiction].
  subst; now left.
Defined.

Lemma L_preadj_sym p p' :
  L_preadj p p' -> L_preadj p' p.
Proof.
  unfold L_preadj.
  intros.
  rewrite file_dist_sym.
  rewrite rank_dist_sym at 1 2.
  auto.
Qed.

Lemma diag_preadj_sym p p' :
  diag_preadj p p' ->
  diag_preadj p' p.
Proof.
  unfold diag_preadj.
  rewrite rank_dist_sym.
  rewrite file_dist_sym at 1; auto.
Qed.

Lemma dist_split x y z :
  x < y < z ->
  Dist.dist x z = Dist.dist x y + Dist.dist y z.
Proof.
  intros [pf1 pf2].
  rewrite (Dist.dist_sym x z).
  rewrite (Dist.dist_sym x y).
  rewrite (Dist.dist_sym y z).
  rewrite StateAction.dist_sub at 1; [|lia].
  rewrite StateAction.dist_sub at 1; [|lia].
  rewrite StateAction.dist_sub at 1; [|lia].
  lia.
Qed.

Lemma file_sbetween_dist_split f1 f2 f3 :
  file_sbetween f1 f2 f3 ->
  file_dist f1 f3 =
  file_dist f1 f2 + file_dist f2 f3.
Proof.
  intros [pf|pf].
  - now apply dist_split.
  - unfold file_dist.
    rewrite (Fin.fin_dist_sym f1 f3).
    rewrite (Fin.fin_dist_sym f1 f2).
    rewrite (Fin.fin_dist_sym f2 f3).
    rewrite PeanoNat.Nat.add_comm.
    now apply dist_split.
Qed.

Lemma rank_sbetween_dist_split r1 r2 r3 :
  rank_sbetween r1 r2 r3 ->
  rank_dist r1 r3 =
  rank_dist r1 r2 + rank_dist r2 r3.
Proof.
  intros [pf|pf].
  - now apply dist_split.
  - unfold rank_dist.
    rewrite (Fin.fin_dist_sym r1 r3).
    rewrite (Fin.fin_dist_sym r1 r2).
    rewrite (Fin.fin_dist_sym r2 r3).
    rewrite PeanoNat.Nat.add_comm.
    now apply dist_split.
Qed.

Lemma diag_adj_sym b p p' :
  diag_adj b p p' ->
  diag_adj b p' p.
Proof.
  intros [pf1 pf2]; split.
  - apply diag_preadj_sym; auto.
  - intros.
    apply pf2.
    + unfold diag_preadj in *.
      apply file_sbetween_dist_split in H0.
      apply rank_sbetween_dist_split in H1.
      rewrite rank_dist_sym.
      rewrite file_dist_sym at 1.
      rewrite rank_dist_sym in pf1.
      rewrite file_dist_sym in pf1 at 1.
      lia.
    + now apply file_sbetween_sym.
    + now apply rank_sbetween_sym.
Qed.

Lemma horiz_preadj_sym p p' :
  horiz_preadj p p' ->
  horiz_preadj p' p.
Proof.
  unfold horiz_preadj; auto.
Qed.

Lemma rank_sbetween_neq_left p1 p2 p3 :
  rank_sbetween (rank p1) (rank p2) (rank p3) ->
  p1 <> p2.
Proof.
  intros [pf|pf]; intro; subst; lia.
Qed.

Lemma rank_sbetween_neq_right p1 p2 p3 :
  rank_sbetween (rank p1) (rank p2) (rank p3) ->
  p2 <> p3.
Proof.
  intros [pf|pf]; intro; subst; lia.
Qed.

Lemma file_sbetween_neq_left p1 p2 p3 :
  file_sbetween (file p1) (file p2) (file p3) ->
  p1 <> p2.
Proof.
  intros [pf|pf]; intro; subst; lia.
Qed.

Lemma file_sbetween_neq_right p1 p2 p3 :
  file_sbetween (file p1) (file p2) (file p3) ->
  p2 <> p3.
Proof.
  intros [pf|pf]; intro; subst; lia.
Qed.

Lemma horiz_preadj_trans p1 p2 p3 :
  horiz_preadj p1 p2 ->
  horiz_preadj p2 p3 ->
  horiz_preadj p1 p3.
Proof.
  unfold horiz_preadj; congruence.
Qed.

Lemma vert_preadj_trans p1 p2 p3 :
  vert_preadj p1 p2 ->
  vert_preadj p2 p3 ->
  vert_preadj p1 p3.
Proof.
  unfold vert_preadj; congruence.
Qed.

Lemma horiz_adj_sym b p p' :
  horiz_adj b p p' ->
  horiz_adj b p' p.
Proof.
  unfold horiz_adj in *.
  intros [pf1 pf2]; split.
  - apply horiz_preadj_sym; auto.
  - intros q Hq1 Hq2.
    apply pf2.
    + apply horiz_preadj_trans with (p2 := p'); auto.
    + destruct Hq2; [now right|now left].
Qed.

Lemma vert_preadj_sym p p' :
  vert_preadj p p' ->
  vert_preadj p' p.
Proof.
  unfold vert_preadj; auto.
Qed.

Lemma vert_adj_sym b p p' :
  vert_adj b p p' ->
  vert_adj b p' p.
Proof.
  unfold vert_adj in *.
  intros [pf1 pf2]; split.
  - apply vert_preadj_sym; auto.
  - intros q Hq1 Hq2.
    apply pf2.
    + apply vert_preadj_trans with (p2 := p'); auto.
    + destruct Hq2; [now right|now left].
Qed.

Lemma orthog_adj_sym b p p' :
  orthog_adj b p p' ->
  orthog_adj b p' p.
Proof.
  unfold orthog_adj in *.
  intros [pfh|pfv]; [left|right].
  - now apply horiz_adj_sym.
  - now apply vert_adj_sym.
Qed.

Lemma diag_orthog_adj_sym b p p' :
  diag_orthog_adj b p p' ->
  diag_orthog_adj b p' p.
Proof.
  intros [pfd|pfo]; [left|right].
  - now apply diag_adj_sym.
  - now apply orthog_adj_sym.
Qed.

Lemma non_pawn_piece_adj_sym pc b p p' :
  non_pawn_piece_adj pc b p p' ->
  non_pawn_piece_adj pc b p' p.
Proof.
  unfold non_pawn_piece_adj.
  destruct pc; intro pf.
  - now apply OnlyKing.neighbor_preadj_sym.
  - now apply diag_orthog_adj_sym.
  - now apply orthog_adj_sym.
  - now apply diag_adj_sym.
  - now apply L_preadj_sym.
Qed.

Lemma non_pawn_piece_adj_update_L pc b p p' o :
  non_pawn_piece_adj pc b p p' ->
  non_pawn_piece_adj pc (Mat.mupdate p o b) p p'.
Proof.
  unfold non_pawn_piece_adj; intro pf; destruct pc; auto.
  - destruct pf as [[pf1 pf2]|[[pf1 pf2]|[pf1 pf2]]].
    + left; unfold diag_adj in *.
      split; auto; intros; unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_left in H0; auto.
    + right; left; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_left in H0; auto.
    + right; right; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply rank_sbetween_neq_left in H0; auto.
  - destruct pf as [[pf1 pf2]|[pf1 pf2]].
    + left; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_left in H0; auto.
    + right; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply rank_sbetween_neq_left in H0; auto.
  - destruct pf as [pf1 pf2]; split; auto; intros.
    unfold lookup_piece.
    rewrite Mat.maccess_mupdate_neq.
    + apply pf2; auto.
    + apply file_sbetween_neq_left in H0; auto.
Qed.

Lemma non_pawn_piece_adj_update_R pc b p p' o :
  non_pawn_piece_adj pc b p p' ->
  non_pawn_piece_adj pc (Mat.mupdate p' o b) p p'.
Proof.
  unfold non_pawn_piece_adj; intro pf; destruct pc; auto.
  - destruct pf as [[pf1 pf2]|[[pf1 pf2]|[pf1 pf2]]].
    + left; unfold diag_adj in *.
      split; auto; intros; unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_right in H0; auto.
    + right; left; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_right in H0; auto.
    + right; right; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply rank_sbetween_neq_right in H0; auto.
  - destruct pf as [[pf1 pf2]|[pf1 pf2]].
    + left; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply file_sbetween_neq_right in H0; auto.
    + right; split; auto; intros.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_neq.
      * apply pf2; auto.
      * apply rank_sbetween_neq_right in H0; auto.
  - destruct pf as [pf1 pf2]; split; auto; intros.
    unfold lookup_piece.
    rewrite Mat.maccess_mupdate_neq.
    + apply pf2; auto.
    + apply file_sbetween_neq_right in H0; auto.
Qed.

Lemma move_reversible c pc b p p' :
  non_pawn_piece_adj pc b p p' ->
  non_pawn_piece_adj pc (clear p (place_piece c pc p' b)) p' p.
Proof.
  intro pf.
  apply non_pawn_piece_adj_update_R.
  apply non_pawn_piece_adj_update_L.
  now apply non_pawn_piece_adj_sym.
Qed.

Lemma reverse_states_correct1 : forall s s',
  In s (reverse_states s') ->
  { m : ChessMove s & exec_ChessMove m = s' }.
Proof.
  intros s s' pf.
  unfold reverse_states in pf; simpl in *.
  apply In_mk_ChessStates_weaken in pf.
  unfold reverse_prestates in pf.
  rewrite filter_In in pf.
  destruct pf as [pf1 pf2].
  rewrite flat_map_concat_map in pf1.
  apply in_concat_sig in pf1.
  destruct pf1 as [ps [pf1 pf3]].
  apply ListUtil.in_map_sig in pf1.
  destruct pf1 as [[pos pc] pf4].
  destruct pf4 as [pf4 pf5].
  rewrite <- pf4 in pf3.
  rewrite flat_map_concat_map in pf3.
  apply in_concat_sig in pf3.
  destruct pf3 as [qs [pf6 pf7]].
  apply ListUtil.in_map_sig in pf6.
  destruct pf6 as [pos' [pf8 pf9]].
  rewrite <- pf8 in pf7.
  apply ListUtil.in_map_sig in pf7.
  destruct pf7 as [o pf11].
  destruct pf11 as [pf11 pf12].
  pose (pm := {|
    piece := pc;
    origin := pos';
    dest := pos;
  |}).
  assert (pos <> pos').
  { rewrite filter_In in pf9.
    destruct pf9 as [pf9 pf13].
    apply candidate_destinations_correct1 in pf9.
    rewrite list_player_pieces_correct in pf5.
    unfold emptyb in pf13.
    intros ?; subst.
    rewrite pf5 in pf13; discriminate.
  }
  assert (legal s pm) as pm_legal.
  { destruct s; inversion pf11; simpl in *; subst; clear pf11.
    split; simpl in *.
    - rewrite lookup_place_eq; auto.
    - unfold open.
      rewrite lookup_place_neq; auto.
      unfold lookup_piece.
      rewrite Mat.maccess_mupdate_eq.
      destruct o; auto.
      destruct p.
      rewrite Player.opp_invol.
      destruct_or; congruence.
    - rewrite filter_In in pf9.
      destruct pf9 as [pf9 _].
      apply candidate_destinations_correct1 in pf9.
      apply non_pawn_piece_adj_update_L.
      apply non_pawn_piece_adj_update_R.
      apply non_pawn_piece_adj_sym; auto.
    - intros p Hp.
      pose proof (Chess.opp_to_play_not_in_check s') as no_threat.
      assert (clear pos'
        (place_piece (Player.opp (chess_to_play s')) pc pos
        (place_piece (Player.opp (chess_to_play s')) pc pos'
        (Mat.mupdate pos o (board s')))) = board s')
        as pf.
      { apply Mat.mat_ext.
        intro c; unfold clear, place_piece.
        destruct (Games.Util.Dec.eq_dec c pos').
        + subst; rewrite Mat.maccess_mupdate_eq.
          rewrite filter_In in pf9.
          destruct pf9 as [_ pf9].
          unfold emptyb in pf9.
          unfold lookup_piece in pf9.
          destruct (Mat.maccess pos' (board s')); auto.
          discriminate.
        + rewrite Mat.maccess_mupdate_neq; auto.
          destruct (Games.Util.Dec.eq_dec c pos).
          * subst; rewrite Mat.maccess_mupdate_eq.
            rewrite list_player_pieces_correct in pf5.
            now symmetry.
          * do 3 (rewrite Mat.maccess_mupdate_neq; auto).
      }
      rewrite pf in *.
      rewrite Player.opp_invol.
      apply no_threat; auto.
  }
  inversion pf11.
  exists (reg_move s {| premove := pm; premove_legal := pm_legal |}).
  unfold exec_ChessMove.
  unfold exec_RegularMove; simpl.
  apply StateAction.state_ext; simpl.
  - rewrite <- H1.
    apply Player.opp_invol.
  - unfold updated_board.
    rewrite <- H1, <- H2; simpl.
    apply Mat.mat_ext.
    unfold clear, place_piece.
    intro c.
    destruct (Games.Util.Dec.eq_dec c pos').
    + subst.
      rewrite Mat.maccess_mupdate_eq.
      rewrite filter_In in pf9.
      destruct pf9 as [_ pf9].
      unfold emptyb in pf9.
      destruct (lookup_piece pos' (board s')) eqn:Hpos'; auto.
      discriminate.
    + rewrite Mat.maccess_mupdate_neq; auto.
      destruct (Games.Util.Dec.eq_dec c pos).
      * subst.
        rewrite Mat.maccess_mupdate_eq.
        rewrite list_player_pieces_correct in pf5; auto.
      * rewrite Mat.maccess_mupdate_neq; auto.
        rewrite Mat.maccess_mupdate_neq; auto.
        rewrite Mat.maccess_mupdate_neq; auto.
  - rewrite <- H1.
    destruct (chess_to_play s'); simpl.
    + congruence.
    + destruct pc; try congruence.
      rewrite list_player_pieces_correct in pf5.
      apply s' in pf5; auto.
  - rewrite <- H1.
    destruct (chess_to_play s'); simpl.
    + destruct pc; try congruence.
      rewrite list_player_pieces_correct in pf5.
      apply s' in pf5; auto.
    + congruence.
Qed.

Lemma reverse_states_correct2 : forall s (m : ChessMove s),
  In s (reverse_states (exec_ChessMove m)).
Proof.
  intros s [[m m_legal]].
  unfold reverse_states.
  apply In_mk_ChessStates_strengthen.
  unfold reverse_prestates.
  rewrite filter_In; split.
  - rewrite in_flat_map.
    exists (dest m, piece m).
    rewrite list_player_pieces_correct; split.
    + simpl; rewrite Player.opp_invol.
      unfold updated_board.
      rewrite lookup_clear_neq;
       [|apply (dest_orig_neq
          {| premove := m; premove_legal := m_legal |})].
      now rewrite lookup_place_eq.
    + rewrite in_flat_map.
      exists (origin m).
      rewrite filter_In; split.
      * split.
        -- apply candidate_destinations_correct2; simpl.
           apply move_reversible; apply m_legal.
        -- unfold emptyb; simpl.
           unfold updated_board.
           now rewrite lookup_clear_eq.
      * rewrite in_map_iff.
        exists (lookup_piece (dest m) (board s)); split.
        -- apply PreChessState_ext; simpl.
           ++ apply Player.opp_invol.
           ++ rewrite Player.opp_invol.
              apply Mat.mat_ext.
              intro c.
              unfold place_piece.
              destruct (Games.Util.Dec.eq_dec c (origin m)).
              ** subst; rewrite Mat.maccess_mupdate_eq.
                 symmetry; apply m_legal.
              ** rewrite Mat.maccess_mupdate_neq; auto.
                 destruct (Games.Util.Dec.eq_dec c (dest m)).
                 --- subst; now rewrite Mat.maccess_mupdate_eq.
                 --- rewrite Mat.maccess_mupdate_neq; auto.
                     unfold updated_board, clear, place_piece.
                     do 2 (rewrite Mat.maccess_mupdate_neq; auto).
           ++ destruct (chess_to_play s) eqn:s_play; auto.
              simpl.
              destruct (piece m) eqn:Hpc; auto.
              pose proof (origin_lookup m_legal) as pf.
              rewrite s_play, Hpc in pf.
              now apply s in pf.
           ++ destruct (chess_to_play s) eqn:s_play; auto.
              simpl.
              destruct (piece m) eqn:Hpc; auto.
              pose proof (origin_lookup m_legal) as pf.
              rewrite s_play, Hpc in pf.
              now apply s in pf.
        -- simpl chess_to_play.
           pose proof (dest_open m_legal) as pf.
           unfold open in pf.
           destruct lookup_piece as [[c pc]|] eqn:Hlookup; subst.
           ++ simpl; destruct pc eqn:Hpc; auto.
              pose proof (no_king_capture
                {| premove := m; premove_legal := m_legal |}
                (Player.opp (chess_to_play s))) as pf; simpl in pf.
              rewrite Hlookup in pf; contradiction.
           ++ simpl; tauto.
  - rewrite Bool.negb_true_iff.
    rewrite <- is_threatened_byb_false_iff.
    unfold PreChessState_of_ChessState.
    unfold pre_king; simpl.
    pose proof (opp_to_play_not_in_check s) as pf.
    destruct (chess_to_play s); apply pf; apply s.
Qed.
