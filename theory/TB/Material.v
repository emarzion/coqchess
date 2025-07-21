Require Import Arith.
Require Import Lia.

Require Import Games.Game.Player.

Require Import Chess.Chess.Chess.

Require Import Games.Util.Dec.

Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.ListUtil.

Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.
Require Import Chess.TB.StateAction.
Require Import Chess.TB.Symmetry.

Fixpoint Vec_count {X} `{Discrete X} {n} (x : X) : Vec X n -> nat :=
  match n with
  | 0 => fun _ => 0
  | S m => fun v =>
    match eq_dec x (fst v) with
    | left _ => S (Vec_count x (snd v))
    | right _ => Vec_count x (snd v)
    end
  end.

Fixpoint Vec_sum {n} : Vec nat n -> nat :=
  match n with
  | 0 => fun _ => 0
  | S m => fun v => fst v + Vec_sum (snd v)
  end.

Lemma Vec_sum_cons {n} (x : nat) (v : Vec nat n) :
  Vec_sum ((x,v) : Vec nat (S n)) = x + Vec_sum v.
Proof.
  reflexivity.
Qed.

Lemma Vec_sum_front_last {n} (v : Vec nat (S n)) :
  Vec_sum v = VecRev.last v + Vec_sum (VecRev.front v).
Proof.
  induction n.
  - reflexivity.
  - destruct v as [x v].
    simpl VecRev.last.
    simpl VecRev.front.
    do 2 rewrite Vec_sum_cons.
    rewrite IHn; lia.
Qed.

Lemma Vec_sum_rev {n} (v : Vec nat n) : Vec_sum (VecRev.rev v) = Vec_sum v.
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite IHn.
    rewrite <- Vec_sum_front_last.
    auto.
Qed.

Lemma Vec_count_cons {X} `{Discrete X} {n} (x y : X) (v : Vec X n) :
  Vec_count x ((y, v) : Vec X (S n)) = if eq_dec x y then S (Vec_count x v) else Vec_count x v.
Proof.
  reflexivity.
Qed.

Lemma Vec_count_place_last {X} `{Discrete X} {n} (x y : X) (v : Vec X n) :
  Vec_count x (VecRev.place_last y v) = if eq_dec x y then S (Vec_count x v) else Vec_count x v.
Proof.
  induction n.
  - reflexivity.
  - destruct v as [z v].
    simpl VecRev.place_last.
    repeat rewrite @Vec_count_cons.
    rewrite IHn.
    destruct (eq_dec x z), (eq_dec x y); auto.
Qed.

Lemma Vec_count_Vec_rev {X} `{Discrete X} {n} (x : X) (v : Vec X n) :
  Vec_count x (VecRev.rev v) = Vec_count x v.
Proof.
  induction n.
  - reflexivity.
  - destruct v as [y v].
    rewrite VecRev.rev_cons.
    rewrite Vec_count_place_last.
    rewrite IHn; auto.
Qed.

Definition Mat_count {X} `{Discrete X} {m n} (x : X) (M : Mat X m n) : nat :=
  Vec_sum (vmap (Vec_count x) M).

Lemma vmap_const {X Y} {n} (y : Y) (v : Vec X n) :
  vmap (fun _ => y) v = vreplicate y.
Proof.
  induction n.
  - reflexivity.
  - simpl; rewrite IHn; auto.
Qed.

Lemma Vec_sum_vreplicate_zero {n} :
  Vec_sum (vreplicate 0 : Vec nat n) = 0.
Proof.
  induction n.
  - reflexivity.
  - simpl; auto.
Qed.

Lemma vmap_cons {X Y} (f : X -> Y) {n} (x : X) (v : Vec X n) : vmap f ((x, v) : Vec X (S n)) = (f x, vmap f v).
Proof.
  reflexivity.
Qed.

Lemma Mat_count_vzip {X} `{Discrete X} {m n} (x : X)
  (c : Vec X m) (M : Mat X m n) :
  Mat_count x (vzip pair c M : Mat X m (S n)) =
  Vec_count x c + Mat_count x M.
Proof.
  induction m.
  - destruct M; auto.
  - destruct c as [y c'].
    destruct M as [d M'].
    simpl vzip.
    unfold Mat_count in *.
    do 2 rewrite vmap_cons.
    do 2 rewrite Vec_sum_cons.
    rewrite IHm.
    simpl Vec_sum.
    simpl Vec_count.
    destruct (eq_dec x y); lia.
Qed.

Lemma Mat_count_transpose {X} `{Discrete X} {m n} (x : X) (M : Mat X m n) :
  Mat_count x (MatAction.transpose M) = Mat_count x M.
Proof.
  induction m.
  - simpl.
    destruct M.
    unfold Mat_count.
    simpl.
    rewrite vmap_const.
    apply Vec_sum_vreplicate_zero.
  - destruct M as [c M'].
    simpl MatAction.transpose.
    rewrite Mat_count_vzip.
    rewrite IHm; auto.
Qed.

Lemma Mat_count_hreflect {X} `{Discrete X} {m n} (x : X) (M : Mat X m n) :
  Mat_count x (MatAction.hreflect M) = Mat_count x M.
Proof.
  unfold Mat_count.
  unfold MatAction.hreflect.
  rewrite <- MatAction.rev_vmap.
  rewrite Vec_sum_rev; auto.
Qed.

Lemma Mat_count_vreflect {X} `{Discrete X} {m n} (x : X) (M : Mat X m n) :
  Mat_count x (MatAction.vreflect M) = Mat_count x M.
Proof.
  unfold Mat_count.
  unfold MatAction.vreflect.
  rewrite vmap_vmap.
  rewrite vmap_ext with (g := Vec_count x); auto.
  apply Vec_count_Vec_rev.
Qed.

Lemma Mat_count_act {X} `{Discrete X} {n} (x : X) (M : Mat X n n) (a : d8_group) :
  Mat_count x (a @ M) = Mat_count x M.
Proof.
  destruct a; simpl.
  - auto.
  - rewrite Mat_count_transpose.
    rewrite Mat_count_hreflect; auto.
  - rewrite Mat_count_vreflect.
    rewrite Mat_count_hreflect; auto.
  - rewrite Mat_count_hreflect.
    rewrite Mat_count_transpose; auto.
  - rewrite Mat_count_hreflect; auto.
  - rewrite Mat_count_vreflect; auto.
  - rewrite Mat_count_transpose; auto.
  - rewrite Mat_count_hreflect.
    rewrite Mat_count_transpose.
    rewrite Mat_count_hreflect; auto.
Qed.

Definition count (c : Player) (p : Piece) (b : Board) : nat :=
  Mat_count (Some (c, p)) b.

Definition material : Type :=
  Player -> Piece -> nat.

Definition KRvK_material : material :=
  fun c p =>
    match c, p with
    | White, King => 1
    | Black, King => 1
    | White, Rook => 1
    | _, _ => 0
    end.

Definition material_bound (m : material) : Game.GameState ChessGame -> Prop :=
  fun s => forall c p, count c p (board s) <= m c p.

Definition KRvK (s : Game.GameState ChessGame) : Prop :=
  material_bound KRvK_material s.

Lemma vaccess_Vec_count_pos {X} `{Discrete X} {n} (x : X)
  (v : Vec X n) (i : Fin.Fin n) :
  Vec.vaccess i v = x ->
  Vec_count x v > 0.
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i as [[]|i]; simpl in *.
    + destruct eq_dec; [lia|].
      congruence.
    + destruct eq_dec; [lia|].
      apply IHn with (i := i); auto.
Qed.

Lemma Vec_count_vupdate_sub {X} `{Discrete X} {n} (x y : X)
  (v : Vec X n) (i : Fin.Fin n) :
  Vec.vaccess i v <> x ->
  Vec.vaccess i v = y ->
  Vec_count y (Vec.vupdate i x v) =
  pred (Vec_count y v).
Proof.
  induction n.
  - destruct i.
  - destruct v as [z v].
    destruct i as [[]|i]; simpl; intros; subst.
    + destruct eq_dec; [contradiction|].
      destruct eq_dec; [|contradiction].
      reflexivity.
    + rewrite IHn; auto.
      destruct eq_dec; auto.
      pose proof (vaccess_Vec_count_pos (Vec.vaccess i v) v i eq_refl).
      lia.
Qed.

Lemma Vec_count_vupdate_add {X} `{Discrete X} {n} (x : X)
  (v : Vec X n) (i : Fin.Fin n) :
  Vec.vaccess i v <> x ->
  Vec_count x (Vec.vupdate i x v) =
  S (Vec_count x v).
Proof.
  induction n.
  - destruct i.
  - destruct v as [z v].
    destruct i as [[]|i]; simpl; intros; subst.
    + destruct eq_dec; [|contradiction].
      destruct eq_dec; [congruence|].
      auto.
    + rewrite IHn; auto.
      destruct eq_dec; auto.
Qed.

Lemma Vec_count_vupdate_no_change {X} `{Discrete X} {n} (x y : X)
  (v : Vec X n) (i : Fin.Fin n) :
  Vec.vaccess i v <> x ->
  Vec.vaccess i v <> y ->
  x <> y ->
  Vec_count y (Vec.vupdate i x v) =
  Vec_count y v.
Proof.
  induction n.
  - destruct i.
  - destruct v as [z v].
    destruct i as [[]|i]; simpl; intros.
    + destruct eq_dec; [congruence|].
      destruct (eq_dec y z); [congruence|].
      auto.
    + rewrite IHn; auto.
Qed.

Lemma Vec_sum_pos {n} (v : Vec nat n) (i : Fin.Fin n) :
  vaccess i v > 0 ->
  Vec_sum v > 0.
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i as [[]|i]; simpl in *.
    + lia.
    + apply IHn in pf; lia.
Qed.

Lemma maccess_Mat_count_pos {X} `{Discrete X} {m n} (x : X)
  (M : Mat X m n) (c : Coord m n) :
  Mat.maccess c M = x ->
  Mat_count x M > 0.
Proof.
  intro pf; destruct c as [i j].
  apply vaccess_Vec_count_pos in pf.
  apply Vec_sum_pos with (i := i).
  rewrite MatAction.vaccess_vmap; auto.
Qed.

Lemma Mat_count_mupdate_sub {X} `{Discrete X} {m n} (x y : X)
  (M : Mat X m n) (c : Coord m n) :
  Mat.maccess c M <> x ->
  Mat.maccess c M = y ->
  Mat_count y (Mat.mupdate c x M) =
  pred (Mat_count y M).
Proof.
  destruct c as [i j].
  unfold maccess, Mat_count, mupdate; simpl.
  induction m.
  - destruct i.
  - destruct M as [c M'].
    destruct i as [[]|i].
    + simpl; intros pf1 pf2.
      rewrite Vec_count_vupdate_sub; auto; simpl.
      apply vaccess_Vec_count_pos in pf2; lia.
    + simpl; intros pf1 pf2.
      rewrite IHm; auto.
      apply maccess_Mat_count_pos with (c := (i,j)) in pf2.
      unfold Mat_count in pf2; lia.
Qed.

Lemma Mat_count_mupdate_add {X} `{Discrete X} {m n} (x : X)
  (M : Mat X m n) (c : Coord m n) :
  Mat.maccess c M <> x ->
  Mat_count x (Mat.mupdate c x M) =
  S (Mat_count x M).
Proof.
  destruct c as [i j].
  unfold maccess, Mat_count, mupdate; simpl.
  induction m.
  - destruct i.
  - destruct M as [c M'].
    destruct i as [[]|i].
    + simpl; intros.
      rewrite Vec_count_vupdate_add; auto.
    + simpl; intros.
      rewrite IHm; auto.
Qed.

Lemma Mat_count_mupdate_no_change {X} `{Discrete X} {m n} (x y : X)
  (M : Mat X m n) (c : Coord m n) :
  Mat.maccess c M <> x ->
  Mat.maccess c M <> y ->
  x <> y ->
  Mat_count y (Mat.mupdate c x M) =
  Mat_count y M.
Proof.
  destruct c as [i j].
  unfold maccess, Mat_count, mupdate; simpl.
  induction m.
  - destruct i.
  - destruct M as [c M'].
    destruct i as [[]|i].
    + simpl; intros.
      rewrite Vec_count_vupdate_no_change; auto.
    + simpl; intros.
      rewrite IHm; auto.
Qed.

Lemma count_exec_move {s} (m : ChessMove s) : forall c p,
  count c p (board (exec_ChessMove m)) <= count c p (board s).
Proof.
  intros; destruct m.
  unfold exec_ChessMove, exec_RegularMove.
  simpl board.
  unfold updated_board, count, clear.
  unfold place_piece.
  destruct (eq_dec (c, p) (chess_to_play s, piece (premove r))) as [Heq|Hneq].
  - rewrite Mat_count_mupdate_sub.
    + rewrite <- Heq.
      rewrite Mat_count_mupdate_add.
      * simpl; lia.
      * pose proof (dest_open (premove_legal r)) as pf.
        intro pf'.
        unfold open in pf.
        unfold lookup_piece in pf.
        rewrite pf' in pf.
        apply (opp_no_fp (chess_to_play s)); congruence.
    + rewrite Mat.maccess_mupdate_neq.
      * rewrite origin_lookup; [|apply r].
        discriminate.
      * intro; apply (dest_orig_neq r); congruence.
    + rewrite Heq.
      rewrite Mat.maccess_mupdate_neq.
      * apply r.
      * intro; apply (dest_orig_neq r); congruence.
  - rewrite Mat_count_mupdate_no_change.
    + destruct (eq_dec (Some (c, p)) (Mat.maccess (dest (premove r)) (board s)))
        as [Heq|Hneq'].
      * rewrite Mat_count_mupdate_sub; auto.
        -- lia.
        -- pose proof (dest_open (premove_legal r)) as pf.
           unfold open in pf.
           intro pf'.
           unfold lookup_piece in pf.
           rewrite pf' in pf.
           apply (opp_no_fp (chess_to_play s)); congruence.
      * rewrite Mat_count_mupdate_no_change; auto.
        -- pose proof (dest_open (premove_legal r)) as pf.
           unfold open in pf.
           intro pf'.
           unfold lookup_piece in pf.
           rewrite pf' in pf.
           apply (opp_no_fp (chess_to_play s)); congruence.
        -- congruence.
    + rewrite Mat.maccess_mupdate_neq.
      * rewrite origin_lookup; [|apply r].
        discriminate.
      * intro; apply (dest_orig_neq r); congruence.
    + rewrite Mat.maccess_mupdate_neq.
      * rewrite origin_lookup; [|apply r].
        congruence.
      * intro; apply (dest_orig_neq r); congruence.
    + discriminate.
Qed.

Lemma count_act x b : forall c p,
  count c p (x @ b) = count c p b.
Proof.
  intros; apply Mat_count_act.
Qed.
