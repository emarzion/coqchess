Require Import Chess.Util.Rel.

Definition sbetween : nat -> nat -> nat -> Prop :=
  fun x y z =>
      (x < y /\ y < z)
   \/ (z < y /\ y < x).

Lemma sbetween_sym : forall x y z,
  sbetween x y z -> sbetween z y x.
Proof.
  unfold sbetween; tauto.
Qed.
