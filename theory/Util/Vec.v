Require Import Arith.
Require Import List.
Import ListNotations.
Import Nat.

Require Import Chess.Util.Fin.
Require Import Chess.Util.UIP.

Fixpoint Vec (X : Type) (n : nat) : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec X m
  end.

Fixpoint vreplicate {X} {n} (x : X) : Vec X n :=
  match n with
  | 0 => tt
  | S m => (x, vreplicate x)
  end.

Fixpoint vaccess {X} {n} : Fin n -> Vec X n -> X :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => fst
    | inr j => fun v => vaccess j (snd v)
    end
  end.

Fixpoint vupdate {X} {n} : Fin n -> X -> Vec X n -> Vec X n :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => fun x v => (x, snd v)
    | inr j => fun x v => (fst v, vupdate j x (snd v))
    end
  end.

Lemma vaccess_vupdate_eq : forall {X} {n}
  (i : Fin n) v (x : X),
  vaccess i (vupdate i x v) = x.
Proof.
  intros X n i v x.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + simpl.
      apply IHn.
Qed.

Lemma vaccess_vupdate_neq : forall {X} {n}
  (i j : Fin n) v (x : X), i <> j ->
  vaccess i (vupdate j x v) = vaccess i v.
Proof.
  intros X n i j v x ij_neq.
  induction n.
  - destruct i.
  - destruct i as [[]|i'];
    destruct j as [[]|j'].
    + now elim ij_neq.
    + reflexivity.
    + reflexivity.
    + simpl.
      apply IHn.
      intro; elim ij_neq.
      congruence.
Qed.

Fixpoint to_list {X} {n} : Vec X n -> list X :=
  match n with
  | 0 => fun _ => []
  | S m => fun v => fst v :: to_list (snd v)
  end.

Fixpoint vmap {X Y} (f : X -> Y) {n} : Vec X n -> Vec Y n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun v => (f (fst v), vmap f (snd v))
  end.

Lemma vmap_vmap {X Y Z} {n} (f : X -> Y) (g : Y -> Z) (v : Vec X n) :
  vmap g (vmap f v) = vmap (fun x => g (f x)) v.
Proof.
  induction n.
  - reflexivity.
  - simpl; now rewrite IHn.
Qed.

Lemma vmap_ext {X Y} {n} (f g : X -> Y) (v : Vec X n) :
  (forall x, f x = g x) ->
  vmap f v = vmap g v.
Proof.
  induction n; intro Hfg.
  - reflexivity.
  - simpl; rewrite Hfg.
    now rewrite IHn.
Qed.

Lemma vmap_id {X} {n} (v : Vec X n) :
  vmap (fun x => x) v = v.
Proof.
  induction n.
  - simpl; now destruct v.
  - destruct v as [x v'].
    simpl; now rewrite IHn.
Qed.

Fixpoint vzip {X Y Z} (f : X -> Y -> Z) {n} : Vec X n -> Vec Y n -> Vec Z n :=
  match n with
  | 0 => fun _ _ => tt
  | S m => fun v w =>
    match v, w with
    | (x,v'), (y,w') => (f x y, vzip f v' w')
    end
  end.
