Require Import Chess.Util.Vec.

Require Import List.
Import ListNotations.

Fixpoint last {X} {n} : Vec X (S n) -> X :=
  match n with
  | 0 => fun v => fst v
  | S m => fun v => last (snd v)
  end.

Fixpoint front {X} {n} : Vec X (S n) -> Vec X n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun v => (fst v, front (snd v))
  end.

Fixpoint rev {X} {n} : Vec X n -> Vec X n :=
  match n with
  | 0 => fun _ => tt
  | S m => fun v => (last v, rev (front v))
  end.

Fixpoint place_last {X} {n} : X -> Vec X n -> Vec X (S n) :=
  match n with
  | 0 => fun x v => (x, v)
  | S m => fun x v => (fst v, place_last x (snd v))
  end.

Lemma rev_cons {X} {n} (x : X) (v : Vec X n) :
  @rev X (S n) (x, v) = place_last x (rev v).
Proof.
  induction n.
  - simpl; now destruct v.
  - simpl; now rewrite <- IHn.
Qed.

Lemma rev_place_last {X} {n} (x : X) (v : Vec X n) :
  rev (place_last x v) = (x, rev v).
Proof.
  induction n.
  - reflexivity.
  - destruct v as [y v'].
    simpl place_last.
    do 2 rewrite @rev_cons.
    now rewrite IHn.
Qed.

Lemma rev_rev {X} {n} : forall v : Vec X n,
  rev (rev v) = v.
Proof.
  induction n; intro.
  - simpl; now destruct v.
  - destruct v as [x v'].
    rewrite rev_cons.
    rewrite rev_place_last.
    now rewrite IHn.
Qed.
