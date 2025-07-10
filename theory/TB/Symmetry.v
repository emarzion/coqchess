Require Import TBGen.StratSymTB.TB.
Require Import TBGen.StratSymTB.OCamlTB.

Require Import Chess.Chess.Chess.
Require Import Chess.TB.StateAction.

Require Import TBGen.Util.Bisim.

Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.

Require Import Games.Util.Dec.

Definition d8_bisim (s1 s2 : ChessState) : Type :=
  { x : d8_group & (x @ s1) = s2 }.

Definition transport {X} (P : X -> Type) {x x' : X} (pf : x = x') (p : P x) : P x' :=
  match pf in (_ = y) return P y with
  | eq_refl => p
  end.

Definition act_premove (x : d8_group) (m : PreMove) : PreMove := {|
  piece := piece m;
  origin := x @ (origin m);
  dest := x @ (dest m);
  |}.

Lemma act_to_play x s :
  chess_to_play (x @ s) = chess_to_play s.
Proof.
  reflexivity.
Qed.

Lemma board_act x s :
  board (x @ s) = (x @ (board s)).
Proof.
  reflexivity.
Qed.

Lemma origin_act x m :
  origin (act_premove x m) = (x @ (origin m)).
Proof.
  reflexivity.
Qed.

Lemma dest_act x m :
  dest (act_premove x m) = (x @ (dest m)).
Proof.
  reflexivity.
Qed.

Lemma piece_act x m :
  piece (act_premove x m) = piece m.
Proof.
  reflexivity.
Qed.

Lemma vupdate_inr {X} {n} (x x' : X)
  (v : Vec.Vec X n) (i : Fin.Fin n) :
  Vec.vupdate (inr i : Fin.Fin (S n)) x' (x, v) = (x, Vec.vupdate i x' v).
Proof.
  reflexivity.
Qed.

Lemma vupdate_last {X} {n} (x x' : X) (v : Vec.Vec X n) :
  Vec.vupdate Fin.last x (VecRev.place_last x' v) =
  VecRev.place_last x v.
Proof.
  induction n.
  - reflexivity.
  - destruct v as [y v'].
    simpl VecRev.place_last.
    simpl Fin.last.
    rewrite @vupdate_inr.
    rewrite IHn; auto.
Qed.

Lemma place_last_vupdate {X} {n} (x x' : X)
  (v : Vec.Vec X n) (i : Fin.Fin n) :
  VecRev.place_last x (Vec.vupdate i x' v) =
  Vec.vupdate (Fin.front i) x' (VecRev.place_last x v).
Proof.
  induction n.
  - destruct i.
  - destruct v as [y v'].
    destruct i as [|j].
    + simpl Vec.vupdate.
      reflexivity.
    + rewrite vupdate_inr.
      simpl; rewrite IHn; auto.
Qed.

Lemma rev_vupdate {X} {n} (x : X) (v : Vec.Vec X n) (i : Fin.Fin n) :
  VecRev.rev (Vec.vupdate i x v) =
  Vec.vupdate (Fin.Fin_rev i) x (VecRev.rev v).
Proof.
  induction n.
  - destruct i.
  - destruct v as [x' v'].
    destruct i as [[]|j].
    + simpl Vec.vupdate at 1.
      do 2 rewrite VecRev.rev_cons.
      rewrite Fin.Fin_rev_inl.
      rewrite vupdate_last; auto.
    + simpl Vec.vupdate at 1.
      do 2 rewrite VecRev.rev_cons.
      rewrite IHn.
      rewrite Fin.Fin_rev_inr.
      rewrite place_last_vupdate; auto.
Qed.

Lemma hreflect_mupdate {X} {m n} (M : Mat.Mat X m n)
  (i : Fin.Fin m) (j : Fin.Fin n) (x : X) :
  MatAction.hreflect (Mat.mupdate (i,j) x M) =
  Mat.mupdate (Fin.Fin_rev i, j) x (MatAction.hreflect M).
Proof.
  unfold MatAction.hreflect.
  unfold Mat.mupdate.
  simpl fst; simpl snd.
  rewrite rev_vupdate.
  rewrite <- MatAction.vaccess_Fin_rev.
  rewrite Fin.Fin_rev_Fin_rev.
  auto.
Qed.

Lemma vmap_vupdate {X Y} (f : X -> Y) {n}
  (i : Fin.Fin n) (v : Vec.Vec X n) (x : X) :
  Vec.vmap f (Vec.vupdate i x v) =
  Vec.vupdate i (f x) (Vec.vmap f v).
Proof.
  induction n.
  - destruct i.
  - destruct v as [x' v'].
    destruct i as [|j].
    + auto.
    + simpl; rewrite IHn; auto.
Qed.

Lemma vreflect_mupdate {X} {m n} (M : Mat.Mat X m n)
  (i : Fin.Fin m) (j : Fin.Fin n) (x : X) :
  MatAction.vreflect (Mat.mupdate (i,j) x M) =
  Mat.mupdate (i, Fin.Fin_rev j) x (MatAction.vreflect M).
Proof.
  unfold MatAction.vreflect.
  unfold Mat.mupdate.
  simpl fst; simpl snd.
  rewrite vmap_vupdate.
  f_equal.
  rewrite rev_vupdate.
  rewrite MatAction.vaccess_vmap.
  auto.
Qed.

Lemma vupdate_vzip {X Y Z} {n} (f : X -> Y -> Z) (x : X) (y : Y)
  (i : Fin.Fin n) (v1 : Vec.Vec X n) (v2 : Vec.Vec Y n) :
  Vec.vupdate i (f x y) (Vec.vzip f v1 v2) =
  Vec.vzip f (Vec.vupdate i x v1) (Vec.vupdate i y v2).
Proof.
  induction n.
  - destruct i.
  - destruct v1 as [x' v1'].
    destruct v2 as [y' v2'].
    destruct i as [|j].
    + auto.
    + simpl; rewrite IHn; auto.
Qed.

Lemma vupdate_vaccess {X} {n} (v : Vec.Vec X n) (i : Fin.Fin n) :
  Vec.vupdate i (Vec.vaccess i v) v = v.
Proof.
  induction n.
  - destruct i.
  - destruct v as [x v'].
    destruct i as [|j].
    + auto.
    + simpl; rewrite IHn; auto.
Qed.

Lemma transpose_mupdate {X} {m n} (M : Mat.Mat X m n)
  (i : Fin.Fin m) (j : Fin.Fin n) (x : X) :
  MatAction.transpose (Mat.mupdate (i,j) x M) =
  Mat.mupdate (j,i) x (MatAction.transpose M).
Proof.
  induction m.
  - destruct i.
  - destruct i as [|i'].
    + destruct M as [c M'].
      unfold Mat.mupdate at 1.
      simpl fst; simpl snd.
      simpl Vec.vupdate.
      simpl MatAction.transpose.
      unfold Mat.mupdate; simpl.
      rewrite vupdate_vzip.
      rewrite MatAction.vaccess_vzip.
      simpl snd.
      rewrite vupdate_vaccess.
      auto.
    + destruct M as [c M'].
      unfold Mat.mupdate at 1.
      simpl fst; simpl snd.
      simpl Vec.vupdate.
      simpl MatAction.transpose.
      unfold Mat.mupdate at 1 in IHm.
      simpl fst in IHm; simpl snd in IHm.
      rewrite IHm.
      unfold Mat.mupdate; simpl.
      rewrite vupdate_vzip.
      rewrite MatAction.vaccess_vzip; simpl.
      rewrite vupdate_vaccess; auto.
Qed.

Lemma mupdate_act {X} {n} (a : d8_group)
  (c : Mat.Coord n n) (x : X) (M : Mat.Mat X n n) :
  (a @ (Mat.mupdate c x M)) = Mat.mupdate (a @ c) x (a @ M).
Proof.
  destruct c as [i j].
  destruct a; simpl.
  - auto.
  - rewrite hreflect_mupdate.
    rewrite transpose_mupdate; auto.
  - rewrite hreflect_mupdate.
    rewrite vreflect_mupdate; auto.
  - rewrite transpose_mupdate.
    rewrite hreflect_mupdate; auto.
  - rewrite hreflect_mupdate; auto.
  - rewrite vreflect_mupdate; auto.
  - rewrite transpose_mupdate; auto.
  - rewrite hreflect_mupdate.
    rewrite transpose_mupdate.
    rewrite hreflect_mupdate; auto.
Qed.

Definition act_premove_legal {s} {x : d8_group} {m : PreMove} :
  legal s m ->
  legal (x @ s) (act_premove x m).
Proof.
  intro pf; constructor.
  - rewrite act_to_play.
    rewrite origin_act.
    rewrite board_act.
    rewrite piece_act.
    unfold lookup_piece.
    rewrite @maccess_act.
    apply pf.
  - rewrite act_to_play.
    rewrite board_act.
    rewrite dest_act.
    unfold open.
    unfold lookup_piece in *.
    rewrite @maccess_act.
    apply pf.
  - rewrite piece_act.
    rewrite board_act.
    rewrite origin_act.
    rewrite dest_act.
    apply non_pawn_piece_adj_act.
    apply pf.
  - intros pos pf1 pf2.
    rewrite origin_act in *.
    rewrite piece_act in *.
    rewrite dest_act in *.
    rewrite act_to_play in *.
    rewrite board_act in *.
    unfold clear, place_piece in *.
    repeat rewrite <- @mupdate_act in *.
    unfold lookup_piece in pf1.
    rewrite @maccess_mat_act in pf1.
    elim (no_resulting_check pf (inv x @ pos)); auto.
    destruct pf2 as [p [piece [pf2 pf3]]].
    exists (inv x @ p), piece; split.
    + unfold lookup_piece in pf2.
      rewrite @maccess_mat_act in pf2; auto.
    + apply non_pawn_piece_adj_act with (x := inv x) in pf3.
      rewrite act_assoc in pf3.
      rewrite inv_left in pf3.
      rewrite act_id in pf3; auto.
Qed.

Definition act_reg_move (x : d8_group) {s} (m : RegularMove s) :
  RegularMove (x @ s) := {|
  premove := act_premove x (premove m);
  premove_legal := act_premove_legal (premove_legal m);
  |}.

Definition act_move (x : d8_group) {s} (m : ChessMove s) :
  ChessMove (x @ s) :=
  match m with
  | reg_move _ m => reg_move _ (act_reg_move x m)
  end.

Lemma exec_act_move x s (m : ChessMove s) :
  exec_ChessMove (act_move x m) =
  (x @ (exec_ChessMove m)).
Proof.
  apply state_ext.
  - rewrite chess_to_play_exec_ChessMove.
    do 2 rewrite act_to_play.
    rewrite chess_to_play_exec_ChessMove; auto.
  - destruct m.
    rewrite board_act.
    simpl.
    unfold updated_board.
    unfold place_piece, clear.
    rewrite board_act.
    rewrite piece_act.
    rewrite origin_act.
    rewrite dest_act.
    do 2 rewrite <- @mupdate_act; auto.
  - destruct m; simpl.
    destruct chess_to_play; auto.
    destruct piece; auto.
  - destruct m; simpl.
    destruct chess_to_play; auto.
    destruct piece; auto.
Qed.

Definition unact_reg_move (x : d8_group) {s} (m : RegularMove (x @ s)) :
  RegularMove s. refine {|
  premove := act_premove (inv x) (premove m);
  premove_legal := _
  |}.
Proof.
  rewrite <- (act_id s) at 1.
  rewrite <- (inv_left _ x).
  rewrite <- act_assoc.
  apply act_premove_legal.
  apply m.
Defined.

Definition unact_move (x : d8_group) {s} (m : ChessMove (x @ s)) :
  ChessMove s :=
  match m with
  | reg_move _ m => reg_move _ (unact_reg_move x m)
  end.

Lemma exec_unact_move x s (m : ChessMove (x @ s)) :
  exec_ChessMove (unact_move x m) =
  (inv x @ (exec_ChessMove m)).
Proof.
  apply state_ext.
  - rewrite chess_to_play_exec_ChessMove.
    rewrite act_to_play.
    rewrite chess_to_play_exec_ChessMove; auto.
  - destruct m.
    rewrite board_act.
    simpl.
    unfold updated_board.
    unfold place_piece, clear.
    rewrite board_act.
    rewrite piece_act.
    rewrite origin_act.
    rewrite dest_act.
    rewrite <- (act_id (board s)) at 1.
    rewrite <- (inv_left _ x).
    rewrite <- act_assoc.
    do 2 rewrite <- @mupdate_act; auto.
  - destruct m; simpl.
    destruct chess_to_play.
    + destruct piece; auto;
      rewrite PosAction.pos_act_assoc;
      rewrite inv_left;
      rewrite PosAction.pos_act_id; auto.
    + rewrite PosAction.pos_act_assoc.
      rewrite inv_left.
      rewrite PosAction.pos_act_id; auto.
  - destruct m; simpl.
    destruct chess_to_play.
    + rewrite PosAction.pos_act_assoc.
      rewrite inv_left.
      rewrite PosAction.pos_act_id; auto.
    + destruct piece; auto;
      rewrite PosAction.pos_act_assoc;
      rewrite inv_left;
      rewrite PosAction.pos_act_id; auto.
Qed.

Lemma PreMove_ext (m1 m2 : PreMove) :
  piece m1 = piece m2 ->
  origin m1 = origin m2 ->
  dest m1 = dest m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl; intros; subst; auto.
Qed.

Lemma act_unact_move x s (m : ChessMove (x @ s)) :
  act_move x (unact_move x m) = m.
Proof.
  destruct m.
  unfold unact_move.
  unfold act_move.
  f_equal.
  apply RegularMove_ext.
  apply PreMove_ext.
  - auto.
  - simpl.
    rewrite PosAction.pos_act_assoc.
    rewrite inv_right.
    rewrite PosAction.pos_act_id; auto.
  - simpl.
    rewrite PosAction.pos_act_assoc.
    rewrite inv_right.
    rewrite PosAction.pos_act_id; auto.
Qed.

Lemma unact_act_move x s (m : ChessMove s) :
  unact_move x (act_move x m) = m.
Proof.
  destruct m.
  unfold unact_move.
  unfold act_move.
  f_equal.
  apply RegularMove_ext.
  apply PreMove_ext.
  - auto.
  - simpl.
    rewrite PosAction.pos_act_assoc.
    rewrite inv_left.
    rewrite PosAction.pos_act_id; auto.
  - simpl.
    rewrite PosAction.pos_act_assoc.
    rewrite inv_left.
    rewrite PosAction.pos_act_id; auto.
Qed.

Lemma act_in_check x s :
  in_check s -> in_check (x @ s).
Proof.
  unfold in_check.
  intros pf pos pf1.
  rewrite act_to_play in *.
  rewrite board_act in *.
  unfold lookup_piece in pf1.
  rewrite @maccess_mat_act in pf1.
  apply pf in pf1.
  destruct pf1 as [p [piece [pf1 pf2]]].
  exists (x @ p), piece; split.
  - unfold lookup_piece.
    rewrite @maccess_act; auto.
  - apply non_pawn_piece_adj_act with (x := x) in pf2.
    rewrite act_assoc in pf2.
    rewrite inv_right in pf2.
    rewrite act_id in pf2; auto.
Qed.

Lemma act_atomic_res x s :
  atomic_chess_res (x @ s) = atomic_chess_res s.
Proof.
  unfold atomic_chess_res.
  destruct (enum_chess_moves (x @ s)) as [|m ms] eqn:Hxs.
  - destruct (enum_chess_moves s) as [|m' ms'] eqn:Hs.
    + do 2 destruct Games.Util.Dec.dec.
      * rewrite act_to_play.
        auto.
      * apply act_in_check with (x := inv x) in i.
        rewrite act_assoc in i.
        rewrite inv_left in i.
        rewrite act_id in i; contradiction.
      * apply act_in_check with (x := x) in i.
        contradiction.
      * auto.
    + pose proof (enum_chess_moves_all (act_move x m')) as pf.
      rewrite Hxs in pf.
      destruct pf.
  - destruct (enum_chess_moves s) eqn:Hs.
    + pose proof (enum_chess_moves_all (unact_move x m)) as pf.
      rewrite Hs in pf.
      destruct pf.
    + auto.
Qed.

Definition d8_InvertibleBisim : InvertibleBisim ChessGame ChessGame.
Proof.
  unshelve econstructor.
  - exact d8_bisim.
  - intros s s' [x Hx] m.
    eapply transport.
    + exact Hx.
    + apply act_move.
      exact m.
  - intros s s' [x Hx] m.
    apply unact_move with (x := x).
    exact (transport ChessMove (eq_sym Hx) m).
  - intros s m s' [x Hx].
    exists (x @ s).
    apply act_move.
    exact m.
  - intros s m s' [x Hx].
    exists (inv x @ s).
    apply act_move.
    exact m.
  - intros s s' [x Hx].
    rewrite <- Hx.
    reflexivity.
  - intros s s' [x Hx].
    rewrite <- Hx.
    simpl.
    rewrite act_atomic_res; auto.
  - intros s s' m [x Hx].
    destruct Hx.
    exists x.
    symmetry.
    simpl.
    apply exec_act_move.
  - intros s s' m [x Hx].
    destruct Hx.
    simpl.
    exists x.
    rewrite exec_unact_move.
    rewrite act_assoc.
    rewrite inv_right.
    apply act_id.
  - intros s s' m [x Hx].
    simpl.
    unfold eq_rect.
    destruct Hx.
    simpl.
    apply act_unact_move.
  - intros s s' m [x Hx].
    simpl.
    destruct Hx.
    simpl.
    apply unact_act_move.
  - intros s s' s'' [x Hx].
    destruct Hx.
    simpl.
    apply exec_act_move.
  - intros s s' s'' [x Hx].
    simpl.
    exists x; auto.
  - intros s m s' [x Hx].
    simpl Game.exec_move in Hx.
    simpl.
    rewrite exec_act_move.
    rewrite <- Hx.
    rewrite act_assoc.
    rewrite inv_left.
    apply act_id.
  - intros s m s' [x Hx].
    exists x.
    unfold projT1.
    rewrite @act_assoc.
    rewrite inv_right.
    apply act_id.
Defined.

Global Instance SymChess : Symmetry ChessGame.
Proof.
  unshelve econstructor.
  - exact d8_InvertibleBisim.
  - admit. (* normalize *)
  - intro s.
    exists id.
    apply act_id.
  - intros s s' [x Hx].
    exists (inv x).
    rewrite <- Hx.
    rewrite act_assoc.
    rewrite inv_left.
    apply act_id.
  - intros s1 s2 s3 [x Hx] [y Hy].
    exists (y # x).
    rewrite <- act_assoc.
    congruence.
  - admit.
  - admit.
Admitted.
