Require Import Lia.
Require Import List.
Import ListNotations.

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

Class Ord (X : Type) := {
  ord_lt : X -> X -> Prop;
  ord_lt_trans : forall x y z, ord_lt x y -> ord_lt y z -> ord_lt x z;
  ord_lt_trich : forall x y, { ord_lt x y } + { x = y} + { ord_lt y x };
  ord_lt_antisym : forall x y, ord_lt x y -> ~ ord_lt y x;
  ord_lt_dec : forall x y, { ord_lt x y } + { ~ ord_lt x y };
  }.

Lemma ord_lt_irref {X} `{Ord X} : forall x,
 ~ ord_lt x x.
Proof.
  intros x pf.
  apply (ord_lt_antisym x x); auto.
Qed.

Definition ord_le {X} `{Ord X} : X -> X -> Prop :=
  fun x y => x = y \/ ord_lt x y.

Lemma ord_le_trans {X} `{Ord X} : forall x y z,
  ord_le x y -> ord_le y z -> ord_le x z.
Proof.
  intros x y z [pf1|pf1] pf2.
  - subst; auto.
  - destruct pf2 as [pf2|pf2].
    + subst; right; auto.
    + right; apply ord_lt_trans with (y := y); auto.
Qed.

Lemma ord_le_antisym {X} `{Ord X} : forall x y,
  ord_le x y -> ord_le y x -> x = y.
Proof.
  intros x y [|] [|]; auto.
  exfalso.
  apply (ord_lt_antisym x y); auto.
Qed.

Instance Ord_Player : Ord Player.Player.
Proof.
  unshelve econstructor.
  - exact (fun p1 p2 => p1 = Player.Black /\ p2 = Player.White).
  - intros x y z; simpl; tauto.
  - intros x y; simpl.
    destruct x; destruct y; tauto.
  - simpl; intros x y [] []; congruence.
  - simpl; intros x y.
    destruct x.
    + right; intros []; congruence.
    + destruct y.
      * left; auto.
      * right; intros []; congruence.
Defined.

Instance Lex_Ord {X Y} `{Ord X, Ord Y} : Ord (X * Y).
Proof.
  unshelve econstructor.
  - exact (fun p p' =>
      ord_lt (fst p) (fst p') \/ (
      fst p = fst p' /\
      ord_lt (snd p) (snd p'))).
  - intros [x1 y1] [x2 y2] [x3 y3]; simpl.
    intros [|[]] [|[]].
    + left; eapply ord_lt_trans; eauto.
    + subst; now left.
    + subst; now left.
    + subst; right; split; auto.
      eapply ord_lt_trans; eauto.
  - intros [x1 y1] [x2 y2]; simpl.
    destruct (ord_lt_trich x1 x2) as [[|]|].
    + now left; left; left.
    + destruct (ord_lt_trich y1 y2) as [[|]|].
      * now left; left; right.
      * left; right; congruence.
      * right; right; split; auto.
    + now right; left.
  - intros [x1 y1] [x2 y2]; simpl.
    intros [|[]] [|[]].
    + eapply (ord_lt_antisym x1); eauto.
    + subst; apply (ord_lt_irref x1); auto.
    + subst; apply (ord_lt_irref x2); auto.
    + eapply (ord_lt_antisym y1); eauto.
  - intros [x1 y1] [x2 y2]; simpl.
    destruct (ord_lt_trich x1 x2) as [[|]|].
    + left; left; auto.
    + destruct (ord_lt_dec y1 y2).
      * now left; right.
      * right; intros [|[]]; auto.
        subst; apply (ord_lt_irref x2); auto.
    + right; intros [|[]].
      * eapply (ord_lt_antisym x1); eauto.
      * subst; apply (ord_lt_irref x2); auto.
Defined.

Instance Fin_Ord {n} : Ord (Fin.Fin n).
Proof.
  unshelve econstructor.
  - exact (fun i j => Fin.val i < Fin.val j).
  - simpl; intros; lia.
  - intros x y.
    destruct (Compare_dec.lt_eq_lt_dec
      (Fin.val x) (Fin.val y)) as [[|]|].
    + now left; left.
    + left; right.
      apply Fin.val_inj; auto.
    + now right.
  - simpl; lia.
  - intros; apply Compare_dec.lt_dec.
Defined.

Instance unit_Ord : Ord unit.
Proof.
  unshelve econstructor.
  - exact (fun _ _ => False).
  - simpl; auto.
  - simpl; intros [] []; auto.
  - simpl; auto.
  - simpl; auto.
Defined.

Instance Vec_Ord {n} {X} `{Ord X} : Ord (Vec.Vec X n).
Proof.
  induction n.
  - exact unit_Ord.
  - apply Lex_Ord.
Defined.

Instance option_Ord {X} `{Ord X} : Ord (option X).
Proof.
  unshelve econstructor.
  - exact (fun o1 o2 =>
      match o1, o2 with
      | None, None => False
      | None, Some _ => True
      | Some _, None => False
      | Some x1, Some x2 => ord_lt x1 x2
      end).
  - simpl; intros x y z pf1 pf2.
    destruct x as [x|].
    + destruct y as [y|]; [|tauto].
      destruct z as [z|]; auto.
      eapply ord_lt_trans; eauto.
    + destruct y as [y|]; [|tauto].
      destruct z; tauto.
  - simpl; intros [x|] [y|].
    + destruct (ord_lt_trich x y) as [[|]|].
      * now left; left.
      * left; right; congruence.
      * now right.
    + now right.
    + now left; left.
    + now left; right.
  - simpl; intros [x|] [y|]; try tauto.
    apply ord_lt_antisym.
  - simpl; intros [x|] [y|]; try tauto.
    apply ord_lt_dec.
Defined.

Definition Piece_val (p : Piece) : nat :=
  match p with
  | King => 0
  | Queen => 1
  | Rook => 2
  | Bishop => 3
  | Knight => 4
  end.

Lemma Piece_val_inj : forall p p', Piece_val p = Piece_val p' -> p = p'.
Proof.
  intros [] []; simpl; auto; discriminate.
Qed.

Instance Piece_Ord : Ord Piece.
Proof.
  unshelve econstructor.
  - exact (fun p p' => Piece_val p < Piece_val p').
  - simpl; intros; lia.
  - intros x y.
    destruct (Compare_dec.lt_eq_lt_dec
      (Piece_val x) (Piece_val y)) as [[|]|].
    + now left; left.
    + left; right.
      apply Piece_val_inj; auto.
    + now right.
  - simpl; lia.
  - intros; apply Compare_dec.lt_dec.
Defined.

Definition ChessState_ord_lt (s1 s2 : ChessState) : Prop :=
  ord_lt (white_king s1) (white_king s2) \/ (
  white_king s1 = white_king s2 /\ (
  ord_lt (black_king s1) (black_king s2) \/ (
  black_king s1 = black_king s2 /\ (
  ord_lt (board s1) (board s2) \/ (
  board s1 = board s2 /\
  ord_lt (chess_to_play s1) (chess_to_play s2)
  ))))).

Fixpoint min_aux {X} `{Ord X} (xs : list X) (def : X) {struct xs} : X :=
  match xs with
  | [] => def
  | x :: xs' =>
    match ord_lt_trich x def with
    | inleft _ => min_aux xs' x
    | inright _ => min_aux xs' def
    end
  end.

Lemma In_min_aux {X} `{Ord X} xs : forall x,
  {In (min_aux xs x) xs} + {min_aux xs x = x}.
Proof.
  induction xs as [|y ys]; intro.
  - now right.
  - simpl.
    destruct ord_lt_trich as [[|]|].
    + destruct (IHys y).
      * left; now right.
      * left; now left.
    + subst.
      destruct (IHys x).
      * left; now right.
      * left; now left.
    + destruct (IHys x).
      * left; now right.
      * now right.
Qed.

Lemma min_aux_le_def {X} `{Ord X} (xs : list X) : forall def,
  ord_le (min_aux xs def) def.
Proof.
  induction xs as [|y ys]; intro.
  - left; auto.
  - simpl.
    destruct ord_lt_trich.
    + apply ord_le_trans with (y := y); auto.
      destruct s; [now right|now left].
    + apply IHys.
Qed.

Lemma In_min_aux_le {X} `{Ord X} (xs : list X) : forall (def : X) (x : X),
  In x xs -> ord_le (min_aux xs def) x.
Proof.
  induction xs as [|y ys]; intros def x pf.
  - destruct pf.
  - destruct pf; simpl; subst.
    + destruct ord_lt_trich.
      * apply min_aux_le_def.
      * apply ord_le_trans with (y := def).
        -- apply min_aux_le_def.
        -- now right.
    + destruct ord_lt_trich; apply IHys; auto.
Qed.

Definition enum_d8 : list d8_group :=
  [i; r90; r180; r270; h; v; d; ad].

Lemma enum_d8_all : forall x,
  In x enum_d8.
Proof.
  destruct x; simpl; firstorder.
Qed.

Global Instance ChessState_Ord : Ord ChessState.
Proof.
  unshelve econstructor.
  - exact ChessState_ord_lt.
  - intros x y z pf1 pf2.
    unfold ChessState_ord_lt in *.
    destruct pf1 as [pf1|[pf1 pf3]].
    + destruct pf2 as [pf2|[pf2 pf3]].
      * left; eapply ord_lt_trans; eauto.
      * left; congruence.
    + rewrite pf1.
      destruct pf2 as [pf4|[pf4 pf5]].
      * left; auto.
      * right; split; auto.
        clear pf1 pf4.
        destruct pf3 as [pf6|[pf6 pf7]].
        -- destruct pf5 as [pf7|[pf7 pf8]].
           ++ left; eapply ord_lt_trans; eauto.
           ++ left; congruence.
        -- rewrite pf6.
           destruct pf5 as [pf8|[pf8 pf9]].
           ++ left; auto.
           ++ right; split; auto.
              clear pf6 pf8.
              destruct pf7 as [pf10|[pf10 pf11]].
              ** destruct pf9 as [pf11|[pf11 pf12]].
                 --- left; eapply ord_lt_trans; eauto.
                 --- left; congruence.
              ** rewrite pf10.
                 destruct pf9 as [pf12|[pf12 pf13]].
                 --- left; auto.
                 --- right; split; auto.
                     eapply ord_lt_trans; eauto.
  - intros x y.
    unfold ChessState_ord_lt.
    destruct (ord_lt_trich (white_king x) (white_king y)) as [[pf1|pf1]|pf1].
    + left; left; left; auto.
    + destruct (ord_lt_trich (black_king x) (black_king y)) as [[pf2|pf2]|pf2].
      * left; left; right; split; auto.
      * destruct (ord_lt_trich (board x) (board y)) as [[pf3|pf3]|pf3].
        -- left; left; right; split; auto.
        -- destruct (ord_lt_trich (chess_to_play x) (chess_to_play y)) as [[pf4|pf4]|pf4].
           ++ left; left; right; split; auto.
           ++ left; right.
              apply state_ext; auto.
           ++ right; right; split; auto.
        -- right; right; split; auto.
      * right; right; split; auto.
    + right; left; auto.
  - intros x y pf1 pf2.
    unfold ChessState_ord_lt in *.
    destruct pf1 as [pf1|[pf1 pf3]].
    + destruct pf2 as [pf2|[pf2 pf4]].
      * eapply ord_lt_antisym with (x := white_king x); eauto.
      * rewrite pf2 in pf1.
        apply (ord_lt_irref (white_king x)); eauto.
    + destruct pf2 as [pf2|[pf2 pf4]].
      * rewrite pf1 in pf2.
        apply (ord_lt_irref (white_king y)); auto.
      * destruct pf3 as [pf3|[pf5 pf6]].
        -- destruct pf4 as [pf4|[pf4 pf5]].
           ++ eapply ord_lt_antisym with (x := black_king x); eauto.
           ++ rewrite pf4 in pf3.
              apply (ord_lt_irref (black_king x)); auto.
        -- destruct pf4 as [pf4|[pf4 pf7]].
           ++ rewrite pf5 in pf4.
              apply (ord_lt_irref (black_king y)); auto.
           ++ destruct pf6 as [pf6|[pf8 pf9]].
              ** destruct pf7 as [pf7|[pf7 pf8]].
                 --- eapply ord_lt_antisym with (x := board x); eauto.
                 --- rewrite pf7 in pf6.
                     apply (ord_lt_irref (board x)); auto.
              ** destruct pf7 as [pf7|[pf10 pf11]].
                 --- rewrite pf8 in pf7.
                     apply (ord_lt_irref (board y)); auto.
                 --- eapply ord_lt_antisym with
                       (x := chess_to_play x); eauto.
  - intros x y.
    unfold ChessState_ord_lt.
    destruct (ord_lt_trich (white_king x) (white_king y))
      as [[pf1|pf1]|pf1].
    + left; left; auto.
    + destruct (ord_lt_trich (black_king x) (black_king y)) as [[pf2|pf2]|pf2].
      * left; right; split; auto.
      * destruct (ord_lt_trich (board x) (board y)) as [[pf3|pf3]|pf3].
        -- left; right; split; auto.
        -- destruct (ord_lt_dec (chess_to_play x) (chess_to_play y)).
           ++ left; right; split; auto.
           ++ right; intros [pf4|[pf4 pf5]].
              ** rewrite pf1 in pf4.
                 apply (ord_lt_irref (white_king y)); auto.
              ** destruct pf5 as [pf5|[pf5 pf6]].
                 --- rewrite pf2 in pf5.
                     apply (ord_lt_irref (black_king y)); auto.
                 --- destruct pf6 as [pf6|[pf7 pf8]]; auto.
                     rewrite pf3 in pf6.
                     apply (ord_lt_irref (board y)); auto.
        -- right; intros [pf4|[pf4 pf5]].
           ++ rewrite pf1 in pf4.
              apply (ord_lt_irref (white_king y)); auto.
           ++ destruct pf5 as [pf5|[pf5 pf6]].
              ** rewrite pf2 in pf5.
                 eapply (ord_lt_irref (black_king y)); auto.
              ** destruct pf6 as [pf6|[pf6 pf7]].
                 --- eapply ord_lt_antisym with (x := board x); eauto.
                 --- rewrite pf6 in pf3.
                     apply (ord_lt_irref (board y)); eauto.
      * right; intros [pf3|[pf3 pf4]].
        -- rewrite pf1 in pf3.
           apply (ord_lt_irref (white_king y)); eauto.
        -- destruct pf4 as [pf4|[pf5 pf6]].
           ++ eapply (ord_lt_antisym (black_king x)); eauto.
           ++ rewrite pf5 in pf2.
              apply (ord_lt_irref (black_king y)); auto.
    + right; intros [pf2|[pf2 pf3]].
      * eapply (ord_lt_antisym (white_king x)); eauto.
      * rewrite pf2 in pf1.
        apply (ord_lt_irref (white_king y)); auto.
Defined.

Global Instance ChessState_Disc : Discrete ChessState.
Proof.
  constructor.
  intros s s'.
  destruct (ord_lt_trich s s') as [[pf|pf]|pf].
  - right.
    intro; subst.
    apply (ord_lt_irref s'); auto.
  - now left.
  - right.
    intro; subst.
    apply (ord_lt_irref s'); auto.
Defined.

Definition normalize : ChessState -> ChessState :=
  fun s => min_aux (map (fun x => x @ s) enum_d8) s.

Lemma in_map_sig {X Y} `{Discrete Y} {f : X -> Y} {xs} {y}
  : In y (map f xs) -> {x : X & f x = y /\ In x xs}.
Proof.
  induction xs as [|x xs'].
  - intros [].
  - intro HIn.
    destruct (eq_dec (f x) y).
    + exists x; split; auto.
      now left.
    + destruct IHxs' as [x' [Hx'1 Hx'2]].
      * destruct HIn; [contradiction|auto].
      * exists x'; split; auto.
        now right.
Defined.

Lemma normalize_act x s :
  normalize (x @ s) = normalize s.
Proof.
  apply ord_le_antisym.
  - apply In_min_aux_le.
    destruct (In_min_aux (map (fun y => y @ s) enum_d8) s).
    + rewrite in_map_iff in *.
      destruct i as [a [Ha _]].
      exists (a # inv x); split.
      * rewrite act_assoc.
        rewrite mult_assoc.
        rewrite inv_left.
        rewrite id_right; auto.
      * apply enum_d8_all.
    + rewrite in_map_iff.
      exists (inv x); split.
      * rewrite act_assoc.
        rewrite inv_left.
        rewrite act_id.
        symmetry; exact e.
      * apply enum_d8_all.
  - apply In_min_aux_le.
    destruct (In_min_aux (map (fun y => y @ (x @ s)) enum_d8) (x @ s)).
    + rewrite in_map_iff in *.
      destruct i as [a [Ha _]].
      exists (a # x); split.
      * rewrite <- act_assoc; auto.
      * apply enum_d8_all.
    + rewrite in_map_iff.
      exists x; split.
      * auto.
      * apply enum_d8_all.
Defined.

Global Instance SymChess : Symmetry ChessGame.
Proof.
  unshelve econstructor.
  - exact d8_InvertibleBisim.
  - exact normalize.
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
  - intros s.
    unfold normalize.
    destruct (In_min_aux
      (map (fun x => x @ s) enum_d8) s).
    + apply in_map_sig in i.
      destruct i as [x [Hx _]].
      exists x; auto.
    + exists i.
      rewrite @act_id.
      symmetry; auto.
  - intros s s' [x Hx].
    rewrite <- Hx.
    rewrite normalize_act; auto.
Defined.
