Require Import Chess.Util.Dec.
Require Import Chess.Util.Fin.
Require Import Chess.Util.Vec.

Require Import List.
Import ListNotations.

Definition Mat (X : Type) (m n : nat) : Type :=
  Vec (Vec X n) m.

Definition mreplicate {X} {m n} (x : X) : Mat X m n :=
  vreplicate (vreplicate x).

Definition Coord m n : Type :=
  Fin m * Fin n.

Definition maccess {X} {m n} : Coord m n -> Mat X m n -> X :=
  fun c mat => vaccess (snd c) (vaccess (fst c) mat).

Definition mupdate {X} {m n} : Coord m n -> X ->
  Mat X m n -> Mat X m n :=
  fun c x mat => vupdate (fst c)
    (vupdate (snd c) x (vaccess (fst c) mat)) mat.

Lemma maccess_mupdate_eq {X} {m n} :
  forall (c : Coord m n) (mat : Mat X m n) (x : X),
  maccess c (mupdate c x mat) = x.
Proof.
  unfold maccess, mupdate.
  intros.
  repeat rewrite vaccess_vupdate_eq; reflexivity.
Qed.

Lemma maccess_mupdate_neq {X} {m n} :
  forall (c1 c2 : Coord m n) (mat : Mat X m n) (x : X),
  c1 <> c2 ->
  maccess c1 (mupdate c2 x mat) =
  maccess c1 mat.
Proof.
  unfold maccess, mupdate.
  intros c1 c2 mat x Hneq.
  destruct (Dec.eq_dec (fst c1) (fst c2)) as [eq1|neq1].
  - rewrite eq1.
    rewrite vaccess_vupdate_eq.
    rewrite vaccess_vupdate_neq; auto.
    intro neq2.
    apply Hneq.
    destruct c1,c2; simpl in *; congruence.
  - rewrite vaccess_vupdate_neq; auto.
Qed.

Definition to_list {X} {m n} (M : Mat X m n) : list X :=
  concat (Vec.to_list (vmap Vec.to_list M)).
