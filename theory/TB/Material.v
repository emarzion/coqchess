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

Definition KRvK_bound (c : Player) (p : Piece) : nat :=
  match c, p with
  | White, King => 1
  | Black, King => 1
  | White, Rook => 1
  | _, _ => 0
  end.

Definition KRvK (s : Game.GameState ChessGame) : Prop :=
  forall c p, count c p (board s) <= KRvK_bound c p.

Lemma count_exec_move {s} (m : ChessMove s) : forall c p,
  count c p (board (exec_ChessMove m)) <= count c p (board s).
Proof.
  unfold exec_ChessMove.
  destruct m.
  unfold exec_RegularMove.
  simpl board.
  unfold updated_board.
Admitted.

Lemma count_act x b : forall c p,
  count c p (x @ b) = count c p b.
Proof.
  intros; apply Mat_count_act.
Qed.
