Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.
Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.VecRev.

Definition hreflect {X} {m n} (M : Mat X m n) : Mat X m n :=
  rev M.

Definition vreflect {X} {m n} (M : Mat X m n) : Mat X m n :=
  vmap rev M.

Fixpoint transpose {X} {m n} {struct m} : Mat X m n -> Mat X n m :=
  match m with
  | 0 => fun _ => vreplicate tt
  | S m' => fun M =>
    match M with
    | (c, M') => vzip pair c (transpose M')
    end
  end.

Lemma hreflect_hreflect {X} {m n} (M : Mat X m n) :
  hreflect (hreflect M) = M.
Proof.
  apply rev_rev.
Qed.

Lemma vreflect_vreflect {X} {m n} (M : Mat X m n) :
  vreflect (vreflect M) = M.
Proof.
  unfold vreflect.
  rewrite vmap_vmap.
  rewrite vmap_ext with (g := fun v => v).
  - apply vmap_id.
  - apply rev_rev.
Qed.

Lemma unit_eq : forall u u' : unit, u = u'.
Proof.
  now destruct u, u'.
Qed.

Lemma vec_unit_eq {n} : forall v v' : Vec unit n,
  v = v'.
Proof.
  induction n; intros.
  - apply unit_eq.
  - destruct v as [x w].
    destruct v' as [x' w'].
    f_equal.
    + apply unit_eq.
    + apply IHn.
Qed.

Lemma transpose_vzip_pair {X} {m n} (M : Mat X m n) (c : Vec X m) :
  @transpose X m (S n) (vzip pair c M) = (c, transpose M).
Proof.
  induction m.
  - simpl; now destruct c.
  - destruct c as [x c'].
    destruct M as [d M'].
    simpl; now rewrite IHm.
Qed.

Lemma transpose_transpose {X} {m n} (M : Mat X m n) :
  transpose (transpose M) = M.
Proof.
  induction m.
  - apply unit_eq.
  - destruct M as [c M'].
    simpl.
    rewrite transpose_vzip_pair.
    now rewrite IHm.
Qed.

Lemma vec_ext {X} {n} (v v' : Vec X n) :
  (forall i, vaccess i v = vaccess i v') -> v = v'.
Proof.
  intro pf.
  induction n.
  - apply unit_eq.
  - destruct v as [x w].
    destruct v' as [x' w'].
    f_equal.
    + apply (pf (inl tt)).
    + apply IHn; intro j.
      apply (pf (inr j)).
Qed.

Lemma vaccess_vmap {X Y} (f : X -> Y) {n} (v : Vec X n) (i : Fin.Fin n) :
  vaccess i (vmap f v) = f (vaccess i v).
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + apply IHn.
Qed.

Lemma vaccess_vzip {X Y Z} (f : X -> Y -> Z) {n}
  (v : Vec X n) (w : Vec Y n) (i : Fin.Fin n) :
  vaccess i (vzip f v w) = f (vaccess i v) (vaccess i w).
Proof.
  induction n.
  - destruct i.
  - destruct v as [x v'].
    destruct w as [y w'].
    destruct i as [[]|j].
    + reflexivity.
    + apply IHn.
Qed.

Lemma mat_ext {X} {m n} (M M' : Mat X m n) :
  (forall i j, maccess i j M = maccess i j M') -> M = M'.
Proof.
  intro pf.
  apply vec_ext; intro i.
  apply vec_ext; intro j.
  apply pf.
Qed.

Lemma maccess_transpose {X} {m n} (M : Mat X m n) i j :
  maccess i j (transpose M) = maccess j i M.
Proof.
  unfold maccess.
  induction m.
  - destruct j.
  - destruct M as [c M'].
    simpl transpose.
    rewrite vaccess_vzip.
    destruct j as [[]|j'].
    + reflexivity.
    + simpl; rewrite IHm; auto.
Qed.

Fixpoint last {n} : Fin.Fin (S n) :=
  match n with
  | 0 => inl tt
  | S m => inr last
  end.

Fixpoint front {n} : Fin.Fin n -> Fin.Fin (S n) :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => inl tt
    | inr j => inr (front j)
    end
  end.

Fixpoint last_or_front {n} (i : Fin.Fin (S n)) :
  { i = last } + { exists j, i = front j }.
Proof.
  induction n.
  - left.
    destruct i as [[]|[]].
    reflexivity.
  - destruct i as [[]|j].
    + right.
      exists (inl tt).
      reflexivity.
    + destruct (IHn j) as [pf|pf].
      * left; rewrite pf; auto.
      * right; destruct pf as [k Hk].
        exists (inr k).
        rewrite Hk; auto.
Defined.

Lemma vaccess_last_place_last {X} {n} (x : X) (v : Vec X n) :
  vaccess last (place_last x v) = x.
Proof.
  induction n.
  - reflexivity.
  - destruct v as [x' v'].
    simpl last; simpl place_last.
    rewrite <- (IHn v') at 2.
    reflexivity.
Qed.

Lemma vaccess_front_place_last {X} {n} (x : X) (v : Vec X n)
  (i : Fin.Fin n) : vaccess (front i) (place_last x v) =
  vaccess i v.
Proof.
  induction n.
  - destruct i.
  - destruct i.
    + simpl. auto.
    + simpl front; simpl place_last.
      apply IHn.
Qed.

Lemma transpose_place_last {X} {m} {n} (M : Mat X m n) (c : Vec X n) :
  transpose (place_last c M) =
  vzip place_last c (transpose M).
Proof.
  apply mat_ext.
  intros i j.
  rewrite maccess_transpose.
  unfold maccess.
  rewrite vaccess_vzip.
  destruct (last_or_front j) as [pf|[k pf]]; subst.
  - do 2 rewrite vaccess_last_place_last.
    reflexivity.
  - do 2 rewrite vaccess_front_place_last.
    symmetry; apply maccess_transpose.
Qed.

Lemma transpose_hreflect {X} {m} {n} : forall (M : Mat X m n),
  transpose (hreflect M) = vreflect (transpose M).
Proof.
  unfold hreflect, vreflect.
  induction m; intro M.
  - apply vec_unit_eq.
  - destruct M as [c M'].
    rewrite rev_cons.
    rewrite transpose_place_last.
    rewrite IHm.
    simpl transpose.
    generalize (transpose M').
    intro N.
    apply vec_ext.
    intro i.
    rewrite vaccess_vzip.
    do 2 rewrite vaccess_vmap.
    rewrite vaccess_vzip.
    rewrite rev_cons.
    reflexivity.
Qed.

Lemma transpose_inj {X} {m n} (M M' : Mat X m n) :
  transpose M = transpose M' -> M = M'.
Proof.
  intro pf.
  apply f_equal with (f := transpose) in pf.
  do 2 rewrite transpose_transpose in pf; auto.
Qed.

Lemma transpose_vreflect {X} {m} {n} : forall (M : Mat X m n),
  transpose (vreflect M) = hreflect (transpose M).
Proof.
  intro M.
  apply transpose_inj.
  rewrite transpose_transpose.
  rewrite transpose_hreflect.
  now rewrite transpose_transpose.
Qed.

Lemma vmap_place_last {X Y} {n} (f : X -> Y) (v : Vec X n) (x : X) :
  vmap f (place_last x v) = place_last (f x) (vmap f v).
Proof.
  induction n.
  - reflexivity.
  - destruct v as [y v'].
    simpl.
    rewrite <- IHn; auto.
Qed.

Lemma rev_vmap {X Y} {n} (f : X -> Y) (v : Vec X n) :
  rev (vmap f v) = vmap f (rev v).
Proof.
  induction n.
  - reflexivity.
  - destruct v as [x w].
    simpl vmap at 1.
    do 2 rewrite rev_cons.
    rewrite vmap_place_last.
    rewrite IHn; auto.
Qed.

Lemma hreflect_vreflect {X} {m} {n} : forall (M : Mat X m n),
  hreflect (vreflect M) = vreflect (hreflect M).
Proof.
  intro M.
  unfold hreflect, vreflect.
  induction m.
  - apply unit_eq.
  - destruct M as [c M'].
    simpl vmap at 1.
    do 2 rewrite rev_cons.
    rewrite vmap_place_last.
    rewrite rev_vmap; auto.
Qed.

Definition mat_act {X} {n} (x : d8_group) (M : Mat X n n) : Mat X n n :=
  match x with
  | i => M
  | r90 => transpose (hreflect M)
  | r180 => vreflect (hreflect M)
  | r270 => hreflect (transpose M)
  | h => hreflect M
  | v => vreflect M
  | d => transpose M
  | ad => hreflect (transpose (hreflect M))
  end.

Lemma mat_act_id {X} {n} : forall (M : Mat X n n),
  mat_act i M = M.
Proof.
  intro M.
  reflexivity.
Qed.

Ltac d8_norm :=
  match goal with
  | |- context[transpose (hreflect ?M)] =>
      rewrite transpose_hreflect; d8_norm
  | |- context[transpose (vreflect ?M)] =>
      rewrite transpose_vreflect; d8_norm
  | |- context[hreflect (hreflect ?M)] =>
      rewrite hreflect_hreflect; d8_norm
  | |- context[vreflect (vreflect ?M)] =>
      rewrite vreflect_vreflect; d8_norm
  | |- context[transpose (transpose ?M)] =>
      rewrite transpose_transpose; d8_norm
  | |- context[hreflect (vreflect ?M)] =>
      rewrite hreflect_vreflect; d8_norm
  | _ => idtac
  end.

Lemma mat_act_assoc {X} {n} : forall (a b : d8_group) (M : Mat X n n), mat_act a (mat_act b M) = mat_act (a # b) M.
Proof.
  intros a b M.
  destruct a, b; simpl; d8_norm; reflexivity.
Qed.

Definition d8_mat_action {X} {n} : GroupAction d8_group (Mat X n n) := {|
  act := mat_act;
  act_id := mat_act_id;
  act_assoc := mat_act_assoc;
  |}.
