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
    Some (pl, Knight)
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

Definition reverse_states (s : ChessState) : list ChessState :=
  mk_ChessStates
    (reverse_prestates s)
    (reverse_prestates_correct1 s)
    (reverse_prestates_correct2 s)
    (reverse_prestates_correct3 s)
    (reverse_prestates_correct4 s).

Lemma reverse_states_correct1 : forall s s',
  In s (reverse_states s') ->
  { m : ChessMove s & exec_ChessMove m = s' }.
Proof.
  intros s s' pf.
  unfold reverse_states in pf; simpl in *.
  apply In_mk_ChessStates_weaken in pf.
  unfold reverse_prestates in pf.
  rewrite filter_In in pf.
  rewrite in_flat_map in pf.
Admitted.

Lemma reverse_states_correct2 : forall s (m : ChessMove s),
  In s (reverse_states (exec_ChessMove m)).
Proof.
  intros s m.
  unfold reverse_states.
  apply In_mk_ChessStates_strengthen.
  unfold reverse_prestates.
  rewrite filter_In; split.
  - admit.
  - rewrite Bool.negb_true_iff.
    rewrite <- is_threatened_byb_false_iff.
    unfold PreChessState_of_ChessState.
    unfold pre_king; simpl.
Admitted.
