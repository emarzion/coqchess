Require Import Chess.Util.Group.

Inductive d8 : Type :=
  | i (* identity *)
  | r90 (* cc 90 degree rotation *)
  | r180 (* cc 180 degree rotation *)
  | r270 (* cc 270 degree rotation *)
  | h (* horizontal reflection *)
  | v (* vertical reflection *)
  | d (* diagonal reflection *)
  | ad (* anti-diagonal reflection *)
  .

Definition d8_mult (x y : d8) : d8 :=
  match x, y with
  | i, _ => y
  | _, i => x
  | r90, r90 => r180
  | r90, r180 => r270
  | r90, r270 => i
  | r90, h => d
  | r90, v => ad
  | r90, d => v
  | r90, ad => h
  | r180, r90 => r270
  | r180, r180 => i
  | r180, r270 => r90
  | r180, h => v
  | r180, v => h
  | r180, d => ad
  | r180, ad => d
  | r270, r90 => i
  | r270, r180 => r90
  | r270, r270 => r180
  | r270, h => ad
  | r270, v => d
  | r270, d => h
  | r270, ad => v
  | h, r90 => ad
  | h, r180 => v
  | h, r270 => d
  | h, h => i
  | h, v => r180
  | h, d => r270
  | h, ad => r90
  | v, r90 => d
  | v, r180 => h
  | v, r270 => ad
  | v, h => r180
  | v, v => i
  | v, d => r90
  | v, ad => r270
  | d, r90 => h
  | d, r180 => ad
  | d, r270 => v
  | d, h => r90
  | d, v => r270
  | d, d => i
  | d, ad => r180
  | ad, r90 => v
  | ad, r180 => d
  | ad, r270 => h
  | ad, h => r270
  | ad, v => r90
  | ad, d => r180
  | ad, ad => i
  end.

Definition d8_inv (x : d8) : d8 :=
  match x with
  | i => i
  | r90 => r270
  | r180 => r180
  | r270 => r90
  | h => h
  | v => v
  | d => d
  | ad => ad
  end.

Lemma d8_id_left : forall x, d8_mult i x = x.
Proof.
  intro; reflexivity.
Qed.

Lemma d8_id_right : forall x, d8_mult x i = x.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Lemma d8_mult_assoc : forall x y z,
  d8_mult (d8_mult x y) z = d8_mult x (d8_mult y z).
Proof.
  intros x y z; destruct x, y, z; reflexivity.
Qed.

Lemma d8_inv_left : forall x,
  d8_mult (d8_inv x) x = i.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Lemma d8_inv_right : forall x,
  d8_mult x (d8_inv x) = i.
Proof.
  intro x; destruct x; reflexivity.
Qed.

Definition d8_group : Group := {|
  carrier := d8;

  id := i;
  mult := d8_mult;
  inv := d8_inv;

  id_left := d8_id_left;
  id_right := d8_id_right;

  mult_assoc := d8_mult_assoc;

  inv_left := d8_inv_left;
  inv_right := d8_inv_right;
  |}.
