Require Import Lia.
Require Import PrimInt63.
Require Import Uint63.
Require Import ZArith.

Require Import List.
Import ListNotations.

Require Import Games.Game.Player.

Require Import Chess.Chess.
Require Import Chess.Util.Fin.

Require Import TBGen.Util.IntHash.

Require Import Chess.TB.Material.Material.
Require Import Chess.TB.MaterialPositions.
Require Import Chess.TB.StateAction.

(*
  The current encoding scheme as described below
  allows for up to 8 pieces using the 63 bits from
  an int value. Given that SOTA for tablebases is 7
  pieces, this should be sufficient.

  64 squares on a chessboard = 6 bits per square.

  1 bit for current player gives 62 left.
  12=6*2 bits for the kings gives 50 left.

  Other than kings, there are eight categories of pieces:
  {Black, White} x {Q,R,B,N}.

  Ideally, we would list all remaining pieces in 6 bit
  regions, but we need a way to demarcate the eight
  piece categories. Therefore, we prepend each position
  with a 0 bit which indicates that the current position
  has another piece, with fencepost 1 bits indicating
  that there are no more pieces in that category and to
  move onto the next one (or terminate the whole process).

  8 fencepost bits give 42 bits left.

  42=7*6 for the remaining 6 pieces exhausts our bit supply.

  Overall, the encoding follows the following diagram:

  [P][WK][BK][WQs][F][WRs][F][WBs][F][WNs][F][BQs][F][BRs][F][BBs][F][BNs][F][0*]

  where

  P = current player
  WK = white king
  BK = black king
  WQs = white queens
  WRs = white rooks
  WBs = white bishops
  WNs = white knights
  BQs = black queens
  BRs = black rooks
  BBs = black bishops
  BNs = black knights
  F = fencepost bit
  0* = zeroes for unused bits

  len(WQs) + len(WRs) + len(WBs) + len(WNs) +
  len(BQs) + len(BRs) + len(BBs) + len(BNs) <= 42

*)

Definition of_nat (n : nat) : int :=
  of_Z (Z.of_nat n).

Definition Zpair (x y : Z) (n : nat) : Z :=
  (x + y * 2^Z.of_nat n)%Z.

Lemma lt_le_iff_lemma : forall x y : Z,
  (x < y)%Z <-> (x + 1 <= y)%Z.
Proof.
  intros x y; split; lia.
Qed.

Lemma Zpair_bound (x y : Z) (m n : nat) :
  (x < 2^Z.of_nat m)%Z ->
  (y < 2^Z.of_nat n)%Z ->
  (Zpair x y m < 2^Z.of_nat (m + n))%Z.
Proof.
  intros Hx Hy.
  unfold Zpair.
  rewrite lt_le_iff_lemma in *.
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r; try lia.
  apply Zmult_le_compat_l with (p := (2^Z.of_nat m)%Z) in Hy; lia.
Qed.

Lemma Zpair_mod (x y : Z) (n : nat) :
  (0 <= x)%Z ->
  (x < 2^Z.of_nat n)%Z ->
  (0 <= y)%Z ->
  ((Zpair x y n) mod 2^Z.of_nat n)%Z = x.
Proof.
  intros.
  unfold Zpair.
  rewrite Z_mod_plus_full.
  rewrite Z.mod_small; auto.
Qed.

Lemma Zpair_shiftr (x y : Z) (n : nat) :
  (0 <= x)%Z ->
  (x < 2^Z.of_nat n)%Z ->
  (0 <= y)%Z ->
  Z.shiftr (Zpair x y n) (Z.of_nat n) = y.
Proof.
  intros pf1 pf2 pf3.
  unfold Zpair.
  rewrite Z.shiftr_div_pow2; [|lia].
  rewrite Z.add_comm.
  rewrite Z.div_add_l.
  - rewrite Z.div_small; lia.
  - lia.
Qed.

Lemma Zpair_correct (x y x' y' : Z) (n : nat) :
  (0 <= x)%Z ->
  (x < 2^Z.of_nat n)%Z ->
  (0 <= x')%Z ->
  (x' < 2^Z.of_nat n)%Z ->
  (0 <= y)%Z ->
  (0 <= y')%Z ->
  Zpair x y n = Zpair x' y' n ->
  x = x' /\ y = y'.
Proof.
  intros Hx1 Hx2 Hx'1 Hx'2 Hy Hy' pf.
  split.
  - apply (f_equal (fun x => Z.modulo x (2^Z.of_nat n))) in pf.
    rewrite Zpair_mod in pf; auto.
    rewrite Zpair_mod in pf; auto.
  - apply (f_equal (fun x => Z.shiftr x (Z.of_nat n))) in pf.
    rewrite Zpair_shiftr in pf; auto.
    rewrite Zpair_shiftr in pf; auto.
Qed.

Definition intpair (x y : int) (n : nat) : int :=
  x + (y << of_nat n).

Lemma simplify_mod_lt x m n :
  (0 <= x ->
  n <= m ->
  x < n ->
  (x mod m) < n)%Z.
Proof.
  intros.
  rewrite Z.mod_small; lia.
Qed.

(*
Lemma simplify_mod_le x m n :
  (0 <= x ->
  n <= m ->
  x < n ->
  (x mod m) < n)%Z.
Proof.
  intros.
  rewrite Z.mod_small; lia.
Qed.
*)



Lemma intpair_bound x y m n :
  (to_Z x < 2^Z.of_nat m)%Z ->
  (to_Z y < 2^Z.of_nat n)%Z ->
  (m + n <= 63) ->
  (to_Z (intpair x y m) < 2^Z.of_nat (m + n))%Z.
Proof.
  intros Hx Hy Hmn.
  unfold intpair.
  rewrite add_spec.
  apply simplify_mod_lt.
  - apply Z.add_nonneg_nonneg; apply to_Z_bounded.
  - apply Z.pow_le_mono_r; unfold size; lia.
  - rewrite lsl_spec.
    unfold of_nat.
    rewrite of_Z_spec.
    rewrite (Z.mod_small (Z.of_nat m)).
    + rewrite Z.mod_small.
      * apply Zpair_bound; auto.
      * split.
        -- apply Z.mul_nonneg_nonneg.
           ++ apply to_Z_bounded.
           ++ apply Z.pow_nonneg; lia.
        -- apply Z.lt_le_trans with (m := (2^(Z.of_nat (n + m)))%Z).
           ++ rewrite Nat2Z.inj_add.
              rewrite Z.pow_add_r; try lia.
              apply Zmult_lt_compat_r; auto; lia.
           ++ apply Z.pow_le_mono_r; unfold size; lia.
    + split; unfold wB; unfold size; lia.
Qed.

Lemma to_Z_intpair x y n :
  n <= 63 ->
  (to_Z x < 2^Z.of_nat n)%Z ->
  (to_Z y < 2^(63 - Z.of_nat n))%Z ->
  (to_Z (intpair x y n) = to_Z x + 2^Z.of_nat n * to_Z y)%Z.
Proof.
  intros Hn Hx Hy.
  unfold intpair.
  unfold of_nat.
  rewrite add_spec.
  rewrite lsl_spec.
  rewrite of_Z_spec.
  rewrite (Z.mod_small (Z.of_nat n)).
  - rewrite (Z.mod_small (φ (y)%uint63 * 2 ^ Z.of_nat n)).
    + rewrite Z.mod_small.
      * lia.
      * split.
        -- apply Z.add_nonneg_nonneg.
           ++ apply to_Z_bounded.
           ++ apply Z.mul_nonneg_nonneg; [|lia].
              apply to_Z_bounded.
        -- unfold wB, size.
           assert (pf : 63%Z = Z.of_nat 63) by reflexivity.
           rewrite pf in Hy.
           rewrite <- Nat2Z.inj_sub in Hy; auto.
           assert (pf' : 63 = n + (63 - n)) by lia.
           rewrite pf'.
           apply Zpair_bound; auto.
    + split.
      * apply Z.mul_nonneg_nonneg; [|lia].
        apply to_Z_bounded.
      * apply Zmult_lt_compat_r with
          (p := (2^Z.of_nat n)%Z) in Hy; [|lia].
        rewrite <- Z.pow_add_r in Hy; try lia.
        rewrite Z.sub_add in Hy; auto.
  - unfold wB, size; lia.
Qed.

Lemma intpair_correct x y n x' y' n' :
  n <= 63 -> n' <= 63 ->
  (to_Z x < 2^Z.of_nat n)%Z ->
  (to_Z x' < 2^Z.of_nat n')%Z ->
  (to_Z y < 2^(63 - Z.of_nat n))%Z ->
  (to_Z y' < 2^(63 - Z.of_nat n'))%Z ->
  n = n' -> intpair x y n = intpair x' y' n' ->
  x = x' /\ y = y'.
Proof.
  intros Hn _ Hx Hx' Hy Hy' ? pf; subst.
  apply (f_equal to_Z) in pf.
  rewrite to_Z_intpair in pf; auto.
  rewrite to_Z_intpair in pf; auto.
  do 2 rewrite (Z.mul_comm (2^(Z.of_nat n'))) in pf.
  apply Zpair_correct in pf; auto; try apply to_Z_bounded.
  destruct pf as [pf1 pf2].
  apply (f_equal of_Z) in pf1.
  apply (f_equal of_Z) in pf2.
  repeat rewrite of_to_Z in *.
  split; auto.
Qed.

Definition hash_Fin {n} (i : Fin n) : int :=
  of_nat (Fin.val i).

(*

    compute in *.
  auto.
 unfold hash_Fin.
    unfold of_nat.
    rewrite of_Z_spec.
    apply simplify_mod_lt.
    + lia.
    + compute; discriminate.
    + assert (pf : (2^Z.of_nat 3 = Z.of_nat 8)%Z) by reflexivity.
      rewrite pf; apply inj_lt.
      apply val_bound.

*)

Lemma hash_Fin_bound {n} : forall i : Fin n,
  (to_Z (hash_Fin i) < Z.of_nat n)%Z.
Proof.
  intro i.
  unfold hash_Fin.
  unfold of_nat.
  rewrite of_Z_spec.
  destruct (Nat.lt_ge_cases n (2^63)).
  - apply simplify_mod_lt.
    + lia.
    + unfold wB, size.
      assert (pf : 2%Z = Z.of_nat 2) by reflexivity.
      rewrite pf.
      rewrite <- inj_pow.
      apply inj_le; lia.
    + apply inj_lt.
      apply val_bound.
  - apply Z.lt_le_trans with (m := wB).
    + apply Z.mod_pos_bound.
      unfold wB; lia.
    + unfold wB, size.
      assert (pf : 2%Z = Z.of_nat 2) by reflexivity.
      rewrite pf.
      rewrite <- inj_pow.
      apply inj_le; lia.
Qed.

Definition hash_Pos (p : Pos) : int :=
  intpair (hash_Fin (fst p)) (hash_Fin (snd p)) 3.

Definition add_Pos (p : Pos) (x : int) : int :=
  intpair (hash_Pos p) x 6.

Fixpoint add_Poss (l : list Pos) (x : int) : int :=
  match l with
  | [] => x
  | p :: l' => add_Pos p (add_Poss l' x)
  end.

Definition hash_PosPad (p : Pos) : int :=
  intpair 1 (hash_Pos p) 1.

Definition add_PosPad (p : Pos) (x : int) : int :=
  intpair (hash_PosPad p) x 7.

Fixpoint add_PosPads (l : list Pos) (x : int) : int :=
  match l with
  | [] => intpair 0 x 1
  | p :: l' => add_PosPad p (add_PosPads l' x)
  end.

Definition hash_Player (p : Player) : int :=
  match p with
  | Black => 0
  | White => 1
  end.

Definition add_Player (p : Player) (x : int) : int :=
  intpair (hash_Player p) x 1.


Lemma hash_Player_small : forall p,
  (to_Z (hash_Player p) < 2)%Z.
Proof.
  intro; destruct p; compute; auto.
Qed.

Lemma hash_Player_inj : forall p p',
  hash_Player p = hash_Player p' ->
  p = p'.
Proof.
  unfold hash_Player.
  intros [] []; auto.
  - intro pf.
    apply (f_equal to_Z) in pf.
    discriminate.
  - intro pf.
    apply (f_equal to_Z) in pf.
    discriminate.
Qed.

Lemma hash_Pos_small : forall p,
  (to_Z (hash_Pos p) < 2^6)%Z.
Proof.
  intro p.
  apply intpair_bound with (n := 3).
  - apply (hash_Fin_bound (fst p)).
  - apply (hash_Fin_bound (snd p)).
  - lia.
Qed.

Lemma hash_Fin_inj {n} (i j : Fin n) :
  n < 2^63 ->
  hash_Fin i = hash_Fin j -> i = j.
Proof.
  intros pf1 pf2.
  unfold hash_Fin in pf2.
  unfold of_nat in *.
  apply (f_equal to_Z) in pf2.
  do 2 rewrite of_Z_spec in pf2.
  rewrite Z.mod_small in pf2.
  - rewrite Z.mod_small in pf2.
    + apply Nat2Z.inj in pf2.
      apply val_inj; auto.
    + split; try lia.
      unfold wB, size.
      assert (pf : 2%Z = Z.of_nat 2) by reflexivity.
      rewrite pf.
      rewrite <- Nat2Z.inj_pow.
      apply inj_lt.
      pose proof (val_bound j); lia.
  - split; try lia.
    unfold wB, size.
    assert (pf : 2%Z = Z.of_nat 2) by reflexivity.
    rewrite pf.
    rewrite <- Nat2Z.inj_pow.
    apply inj_lt.
    pose proof (val_bound i); lia.
Qed.

Lemma hash_Pos_inj : forall p p',
  hash_Pos p = hash_Pos p' -> p = p'.
Proof.
  intros [i j] [i' j'] pf.
  unfold hash_Pos in pf.
  apply intpair_correct in pf; try lia.
  - simpl in pf.
    destruct pf as [pf1 pf2].
    apply hash_Fin_inj in pf1; subst.
    + apply hash_Fin_inj in pf2; subst; auto.
      rewrite Nat.log2_lt_pow2; compute; lia.
    + rewrite Nat.log2_lt_pow2; compute; lia.
  - apply (hash_Fin_bound i).
  - apply (hash_Fin_bound i').
  - eapply Z.lt_le_trans;
      [apply hash_Fin_bound|lia].
  - eapply Z.lt_le_trans;
      [apply hash_Fin_bound|lia].
Qed.

Lemma add_Pos_bound n p x :
  (to_Z x < 2^Z.of_nat n)%Z ->
  6 + n <= 63 ->
  (to_Z (add_Pos p x) < 2^(Z.of_nat (6 + n)))%Z.
Proof.
  unfold add_Pos.
  intros.
  apply intpair_bound; auto.
  apply hash_Pos_small.
Qed.

Lemma hash_PosPad_small : forall p,
  (to_Z (hash_PosPad p) < 2^7)%Z.
Proof.
  intro.
  unfold hash_PosPad.
  apply intpair_bound with (n := 6).
  - compute; auto.
  - apply hash_Pos_small.
  - lia.
Qed.

Lemma add_PosPad_bound n p x :
  (to_Z x < 2^Z.of_nat n)%Z ->
  7 + n <= 63 ->
  (to_Z (add_PosPad p x) < 2^(Z.of_nat (7 + n)))%Z.
Proof.
  unfold add_PosPad.
  intros.
  apply intpair_bound; auto.
  apply hash_PosPad_small.
Qed.

Lemma add_PosPads_bound n l x :
  (to_Z x < 2^Z.of_nat n)%Z ->
  (length l) * 7 + 1 + n <= 63 ->
  (to_Z (add_PosPads l x) < 2^(Z.of_nat ((length l) * 7 + 1 + n)))%Z.
Proof.
  induction l as [|p l']; intros Hx Hn.
  - simpl (length [] * 7 + 1 + n).
    simpl add_PosPads.
    apply intpair_bound; compute; auto.
  - simpl length in *.
    simpl add_PosPads.
    rewrite Nat.mul_succ_l.
    rewrite (Nat.add_comm _ 7).
    rewrite <- (Nat.add_assoc 7).
    apply add_PosPad_bound with (n := (length l' * 7 + 1) + n).
    + apply IHl'; auto; lia.
    + lia.
Qed.

Definition BN m : int :=
  add_PosPads
    (m Black Knight)
    0.
(*here*)

Definition PosPad_size (m : material_positions) c p : nat :=
  length (m c p) * 7 + 1.

Lemma add_Poss_bound n l x :
  (to_Z x < 2^Z.of_nat n)%Z ->
  (length l) * 6 + n <= 63 ->
  (to_Z (add_Poss l x) < 2^(Z.of_nat ((length l) * 6 + n)))%Z.
Proof.
  induction l as [|p l']; intros Hx Hn.
  - simpl; auto.
  - simpl add_Poss.
    simpl length.
    rewrite Nat.mul_succ_l.
    rewrite (Nat.add_comm _ 6).
    rewrite <- Nat.add_assoc.
    apply add_Pos_bound.
    + apply IHl'.
      * auto.
      * simpl length in Hn; lia.
    + simpl length in Hn; lia.
Qed.

Lemma add_Poss_correct ps : forall ps' x x',
  length ps = length ps' ->
  length ps * 6 <= 63 ->
  (to_Z x < 2^(Z.of_nat (63 - (length ps) * 6)))%Z ->
  (to_Z x' < 2^(Z.of_nat (63 - (length ps') * 6)))%Z ->
  add_Poss ps x = add_Poss ps' x' ->
  ps = ps' /\ x = x'.
Proof.
  induction ps as [|p tl]; intros ps' x x' eq_len len_bound Hx Hx' Hxx'.
  - destruct ps' as [|p' tl'].
    + split; auto.
    + discriminate.
  - destruct ps' as [|p' tl'].
    + discriminate.
    + simpl in Hxx'.
      apply intpair_correct in Hxx'; try lia.
      * destruct Hxx' as [pf1 pf2].
        apply hash_Pos_inj in pf1; subst.
        apply IHtl in pf2.
        -- destruct pf2; split; auto; congruence.
        -- inversion eq_len; auto.
        -- simpl length in len_bound; lia.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; simpl length; lia.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; simpl length; lia.
      * apply hash_Pos_small.
      * apply hash_Pos_small.
      * apply add_Poss_bound with (l := tl) in Hx.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; [lia|].
           simpl length in *; lia.
        -- simpl length in *; lia.
      * apply add_Poss_bound with (l := tl') in Hx'.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; [lia|].
           simpl length in *; lia.
        -- simpl length in *; lia.
Qed.

Lemma hash_PosPad_inj : forall p p',
  hash_PosPad p = hash_PosPad p' -> p = p'.
Proof.
  intros p p' pf.
  unfold hash_PosPad in pf.
  apply intpair_correct in pf; try lia.
  - destruct pf as [_ pf].
    apply hash_Pos_inj; auto.
  - compute; auto.
  - compute; auto.
  - eapply Z.lt_le_trans.
    + apply hash_Pos_small.
    + lia.
  - eapply Z.lt_le_trans.
    + apply hash_Pos_small.
    + lia.
Qed.

Lemma intpair_zero : forall n,
  intpair 0 0 n = 0%uint63.
Proof.
  intro n; unfold intpair.
  rewrite lsl0; auto.
Qed.

Lemma negb_inj x y : negb x = negb y ->
  x = y.
Proof.
  intro; destruct x, y; auto.
Qed.

Lemma b2i_inj x y :
  b2i x = b2i y -> x = y.
Proof.
  destruct x, y; auto; intro pf;
  apply (f_equal to_Z) in pf;
  discriminate.
Qed.

Lemma bit0_add x y :
  bit (x + y) 0 =
  xorb (bit x 0) (bit y 0).
Proof.
  pose proof (bit_0_spec x) as Hx.
  pose proof (bit_0_spec y) as Hy.
  pose proof (bit_0_spec (x+y)) as Hxy.
  rewrite add_spec in Hxy.
  rewrite <- Znumtheory.Zmod_div_mod in Hxy;
    unfold wB; try lia.
  - rewrite Zplus_mod in Hxy.
    rewrite <- Hx in Hxy.
    rewrite <- Hy in Hxy.
    destruct (bit x 0), (bit y 0), (bit (x + y) 0);
      auto; discriminate.
  - exists (2^62)%Z; auto.
Qed.

Lemma add_PosPads_correct ps : forall ps' x x',
  length ps * 7 + 1 <= 63 ->
  length ps' * 7 + 1 <= 63 ->
  (to_Z x < 2^(Z.of_nat (63 - ((length ps) * 7 + 1))))%Z ->
  (to_Z x' < 2^(Z.of_nat (63 - ((length ps') * 7 + 1))))%Z ->
  add_PosPads ps x = add_PosPads ps' x' ->
  ps = ps' /\ x = x'.
Proof.
  induction ps as [|p tl]; intros ps' x x' Hlen Hlen' Hx Hx' Hxx'.
  - destruct ps'.
    + split; auto. simpl in Hxx'.
      apply intpair_correct in Hxx'; auto.
      * tauto.
      * compute; auto.
      * compute; auto.
    + simpl in Hxx'.
      apply (f_equal (fun z => (bit z 0))) in Hxx'.
      unfold add_PosPad in Hxx'.
      unfold hash_PosPad in Hxx'.
      unfold intpair in Hxx'.
      repeat rewrite bit0_add in Hxx'.
      rewrite bit_1 in Hxx'.
      simpl in Hxx'.
      repeat rewrite bit_lsl in Hxx'.
      discriminate.
  - destruct ps'.
    + simpl in Hxx'.
      apply (f_equal (fun z => (bit z 0))) in Hxx'.
      unfold add_PosPad in Hxx'.
      unfold hash_PosPad in Hxx'.
      unfold intpair in Hxx'.
      repeat rewrite bit0_add in Hxx'.
      rewrite bit_1 in Hxx'.
      simpl in Hxx'.
      repeat rewrite bit_lsl in Hxx'.
      discriminate.
    + simpl in Hxx'.
      apply intpair_correct in Hxx'; try lia.
      * destruct Hxx' as [pf1 pf2].
        apply hash_PosPad_inj in pf1.
        apply IHtl in pf2.
        -- destruct pf2; split; congruence.
        -- simpl length in Hlen; lia.
        -- simpl length in Hlen'; lia.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; simpl length; lia.
        -- eapply Z.lt_le_trans; eauto.
           apply Z.pow_le_mono_r; simpl length; lia.
      * apply hash_PosPad_small.
      * apply hash_PosPad_small.
      * eapply Z.lt_le_trans.
        -- apply add_PosPads_bound; eauto.
           simpl length in *; lia.
        -- apply Z.pow_le_mono_r; simpl length in *; lia.
      * eapply Z.lt_le_trans.
        -- apply add_PosPads_bound; eauto.
           simpl length in *. lia.
        -- apply Z.pow_le_mono_r; simpl length in *; lia.
Qed.

Ltac get_bounds p :=
  pose proof (p Black Knight);
  pose proof (p Black Bishop);
  pose proof (p Black Rook);
  pose proof (p Black Queen);
  pose proof (p White Knight);
  pose proof (p White Bishop);
  pose proof (p White Rook);
  pose proof (p White Queen).

Ltac reason_bounds p :=
  unfold PosPad_size;
  repeat rewrite mp_of_board_count;
  get_bounds p; lia.

Lemma BN_bound m :
  let size :=
    PosPad_size m Black Knight in
  size <= 63 ->
  (to_Z (BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - apply add_PosPads_bound with (n := 0).
    + apply Z.pow_pos_nonneg; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma BN_correct m m' :
  let size :=
    PosPad_size m Black Knight in
  let size' :=
    PosPad_size m' Black Knight in
  size <= 63 -> size' <= 63 ->
  BN m = BN m' ->
  m Black Knight = m' Black Knight.
Proof.
  simpl; intros.
  apply add_PosPads_correct in H1; auto.
  - tauto.
  - apply Z.pow_pos_nonneg; lia.
  - apply Z.pow_pos_nonneg; lia.
Qed.

Definition BB_BN m : int :=
  add_PosPads
    (m Black Bishop)
    (BN m).

Lemma BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop in
  size <= 63 ->
  (to_Z (BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop in
  size <= 63 -> size' <= 63 ->
  BB_BN m = BB_BN m' ->
  m Black Bishop = m' Black Bishop /\
  BN m = BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition BR_BB_BN m : int :=
  add_PosPads
    (m Black Rook)
    (BB_BN m).

Lemma BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook in
  size <= 63 ->
  (to_Z (BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook in
  size <= 63 -> size' <= 63 ->
  BR_BB_BN m = BR_BB_BN m' ->
  m Black Rook = m' Black Rook /\
  BB_BN m = BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition BQ_BR_BB_BN m : int :=
  add_PosPads
    (m Black Queen)
    (BR_BB_BN m).

Lemma BQ_BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen in
  size <= 63 ->
  (to_Z (BQ_BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply BR_BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma BQ_BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook +
    PosPad_size m' Black Queen in
  size <= 63 -> size' <= 63 ->
  BQ_BR_BB_BN m = BQ_BR_BB_BN m' ->
  m Black Queen = m' Black Queen /\
  BR_BB_BN m = BR_BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition WN_BQ_BR_BB_BN m : int :=
  add_PosPads
    (m White Knight)
    (BQ_BR_BB_BN m).

Lemma WN_BQ_BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight in
  size <= 63 ->
  (to_Z (WN_BQ_BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma WN_BQ_BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook +
    PosPad_size m' Black Queen +
    PosPad_size m' White Knight in
  size <= 63 -> size' <= 63 ->
  WN_BQ_BR_BB_BN m = WN_BQ_BR_BB_BN m' ->
  m White Knight = m' White Knight /\
  BQ_BR_BB_BN m = BQ_BR_BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition WB_WN_BQ_BR_BB_BN m : int :=
  add_PosPads
    (m White Bishop)
    (WN_BQ_BR_BB_BN m).

Lemma WB_WN_BQ_BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop in
  size <= 63 ->
  (to_Z (WB_WN_BQ_BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma WB_WN_BQ_BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook +
    PosPad_size m' Black Queen +
    PosPad_size m' White Knight +
    PosPad_size m' White Bishop in
  size <= 63 -> size' <= 63 ->
  WB_WN_BQ_BR_BB_BN m = WB_WN_BQ_BR_BB_BN m' ->
  m White Bishop = m' White Bishop /\
  WN_BQ_BR_BB_BN m = WN_BQ_BR_BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition WR_WB_WN_BQ_BR_BB_BN m : int :=
  add_PosPads
    (m White Rook)
    (WB_WN_BQ_BR_BB_BN m).

Lemma WR_WB_WN_BQ_BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop +
    PosPad_size m White Rook in
  size <= 63 ->
  (to_Z (WR_WB_WN_BQ_BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma WR_WB_WN_BQ_BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop +
    PosPad_size m White Rook in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook +
    PosPad_size m' Black Queen +
    PosPad_size m' White Knight +
    PosPad_size m' White Bishop +
    PosPad_size m' White Rook in
  size <= 63 -> size' <= 63 ->
  WR_WB_WN_BQ_BR_BB_BN m = WR_WB_WN_BQ_BR_BB_BN m' ->
  m White Rook = m' White Rook /\
  WB_WN_BQ_BR_BB_BN m = WB_WN_BQ_BR_BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition WQ_WR_WB_WN_BQ_BR_BB_BN m : int :=
  add_PosPads
    (m White Queen)
    (WR_WB_WN_BQ_BR_BB_BN m).

Lemma WQ_WR_WB_WN_BQ_BR_BB_BN_bound m :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop +
    PosPad_size m White Rook +
    PosPad_size m White Queen in
  size <= 63 ->
  (to_Z (WQ_WR_WB_WN_BQ_BR_BB_BN m) < 2^Z.of_nat size)%Z.
Proof.
  simpl;
  intros Hm.
  eapply Z.lt_le_trans.
  - eapply add_PosPads_bound.
    + apply WR_WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *; lia.
  - unfold PosPad_size in *.
    apply Z.pow_le_mono_r; lia.
Qed.

Lemma WQ_WR_WB_WN_BQ_BR_BB_BN_correct m m' :
  let size :=
    PosPad_size m Black Knight +
    PosPad_size m Black Bishop +
    PosPad_size m Black Rook +
    PosPad_size m Black Queen +
    PosPad_size m White Knight +
    PosPad_size m White Bishop +
    PosPad_size m White Rook +
    PosPad_size m White Queen in
  let size' :=
    PosPad_size m' Black Knight +
    PosPad_size m' Black Bishop +
    PosPad_size m' Black Rook +
    PosPad_size m' Black Queen +
    PosPad_size m' White Knight +
    PosPad_size m' White Bishop +
    PosPad_size m' White Rook +
    PosPad_size m' White Queen in
  size <= 63 -> size' <= 63 ->
  WQ_WR_WB_WN_BQ_BR_BB_BN m = WQ_WR_WB_WN_BQ_BR_BB_BN m' ->
  m White Queen = m' White Queen /\
  WR_WB_WN_BQ_BR_BB_BN m = WR_WB_WN_BQ_BR_BB_BN m'.
Proof.
  simpl; intros.
  apply add_PosPads_correct; auto.
  - unfold PosPad_size in *; lia.
  - unfold PosPad_size in *; lia.
  - eapply Z.lt_le_trans.
    + apply WR_WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + apply WR_WB_WN_BQ_BR_BB_BN_bound; lia.
    + unfold PosPad_size in *.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition kingless_material_size (m : material) : nat :=
  m White Queen +
  m White Rook +
  m White Bishop +
  m White Knight +

  m Black Queen +
  m Black Rook +
  m Black Bishop +
  m Black Knight.

Lemma kingless_50 m s:
  kingless_material_size m <= 6 ->
  material_bound m s ->
  (to_Z (WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s))) < 2^50)%Z.
Proof.
  intros pf1 pf2.
  assert (
    PosPad_size (mp_of_board (board s)) Black Knight +
    PosPad_size (mp_of_board (board s)) Black Bishop +
    PosPad_size (mp_of_board (board s)) Black Rook +
    PosPad_size (mp_of_board (board s)) Black Queen +
    PosPad_size (mp_of_board (board s)) White Knight +
    PosPad_size (mp_of_board (board s)) White Bishop +
    PosPad_size (mp_of_board (board s)) White Rook +
    PosPad_size (mp_of_board (board s)) White Queen <= 50
  ).
  { unfold PosPad_size.
    repeat rewrite mp_of_board_count.
    unfold kingless_material_size in pf1.
    pose proof (pf2 Black Knight).
    pose proof (pf2 Black Bishop).
    pose proof (pf2 Black Rook).
    pose proof (pf2 Black Queen).
    pose proof (pf2 White Knight).
    pose proof (pf2 White Bishop).
    pose proof (pf2 White Rook).
    pose proof (pf2 White Queen).
    lia.
  }
  eapply Z.lt_le_trans.
  - apply WQ_WR_WB_WN_BQ_BR_BB_BN_bound; lia.
  - apply Z.pow_le_mono_r; lia.
Qed.

Definition BK_WQ_WR_WB_WN_BQ_BR_BB_BN m : int :=
  add_Poss
    (m Black King)
    (WQ_WR_WB_WN_BQ_BR_BB_BN m).

Lemma BK_WQ_WR_WB_WN_BQ_BR_BB_BN_bound m s :
  kingless_material_size m <= 6 ->
  material_bound m s ->
  (to_Z (BK_WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s))) < 2^56)%Z.
Proof.
  intros Hm1 Hm2.
  eapply Z.lt_le_trans.
  - apply add_Poss_bound with (n := 50).
    + eapply kingless_50; eauto.
    + rewrite mp_of_board_count.
      rewrite king_count; lia.
  - rewrite mp_of_board_count.
    rewrite king_count; lia.
Qed.

Lemma BK_WQ_WR_WB_WN_BQ_BR_BB_BN_correct m s s' :
  kingless_material_size m <= 6 ->
  material_bound m s ->
  material_bound m s' ->

  BK_WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s)) =
  BK_WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s')) ->

  mp_of_board (board s) Black King = mp_of_board (board s') Black King /\
  WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s)) = WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s')).
Proof.
  intros Hm1 Hm2 Hm3 pf.
  unfold kingless_material_size in Hm1.
  apply add_Poss_correct; auto.
  - do 2 rewrite mp_of_board_count.
    do 2 rewrite king_count; auto.
  - rewrite mp_of_board_count.
    rewrite king_count; lia.
  - eapply Z.lt_le_trans.
    + apply WQ_WR_WB_WN_BQ_BR_BB_BN_bound.
      reason_bounds Hm2.
    + apply Z.pow_le_mono_r; [lia|].
      rewrite mp_of_board_count.
      rewrite king_count.
      reason_bounds Hm2.
  - rewrite mp_of_board_count.
    rewrite king_count.
    eapply Z.lt_le_trans.
    + apply WQ_WR_WB_WN_BQ_BR_BB_BN_bound.
      reason_bounds Hm3.
    + apply Z.pow_le_mono_r; [lia|].
      reason_bounds Hm3.
Qed.

Definition hash_mp m : int :=
  add_Poss
    (m White King)
    (BK_WQ_WR_WB_WN_BQ_BR_BB_BN m).

Lemma hash_mp_bound m s :
  kingless_material_size m <= 6 ->
  material_bound m s ->
  (to_Z (hash_mp (mp_of_board (board s))) < 2^62)%Z.
Proof.
  intros Hm1 Hm2.
  eapply Z.lt_le_trans.
  - apply add_Poss_bound with (n := 56).
    + eapply BK_WQ_WR_WB_WN_BQ_BR_BB_BN_bound; eauto.
    + rewrite mp_of_board_count.
      rewrite king_count; lia.
  - rewrite mp_of_board_count.
    rewrite king_count; lia.
Qed.

Lemma hash_mp_correct m s s' :
  kingless_material_size m <= 6 ->
  material_bound m s ->
  material_bound m s' ->

  hash_mp (mp_of_board (board s)) =
  hash_mp (mp_of_board (board s')) ->

  mp_of_board (board s) White King = mp_of_board (board s') White King /\
  BK_WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s)) = BK_WQ_WR_WB_WN_BQ_BR_BB_BN (mp_of_board (board s')).
Proof.
  intros Hm1 Hm2 pf.
  apply add_Poss_correct; auto.
  - do 2 rewrite mp_of_board_count.
    do 2 rewrite king_count; auto.
  - rewrite mp_of_board_count.
    rewrite king_count; lia.
  - eapply Z.lt_le_trans.
    + eapply BK_WQ_WR_WB_WN_BQ_BR_BB_BN_bound; eauto.
    + rewrite mp_of_board_count.
      rewrite king_count.
      apply Z.pow_le_mono_r; lia.
  - eapply Z.lt_le_trans.
    + eapply BK_WQ_WR_WB_WN_BQ_BR_BB_BN_bound; eauto.
    + rewrite mp_of_board_count.
      rewrite king_count.
      apply Z.pow_le_mono_r; lia.
Qed.

Definition hash_state (s : ChessState) : int :=
  add_Player (chess_to_play s) (hash_mp (mp_of_board (board s))).

Lemma hash_state_correct (m : material) :
  kingless_material_size m <= 6 ->
  forall s s',
  material_bound m s ->
  material_bound m s' ->
  hash_state s = hash_state s' ->
  s = s'.
Proof.
  intros m_bound s s' s_bound s'_bound Hss'.
  unfold kingless_material_size in m_bound.
  apply intpair_correct in Hss'; try lia.
  - destruct Hss' as [eq1 Hss'].
    apply hash_mp_correct with (m := m) in Hss'; auto.
    destruct Hss' as [eq2 Hss'].
    apply BK_WQ_WR_WB_WN_BQ_BR_BB_BN_correct with (m := m) in Hss'; auto.
    destruct Hss' as [eq3 Hss'].
    apply WQ_WR_WB_WN_BQ_BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq4 Hss'].
    apply WR_WB_WN_BQ_BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq5 Hss'].
    apply WB_WN_BQ_BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq6 Hss'].
    apply WN_BQ_BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq7 Hss'].
    apply BQ_BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq8 Hss'].
    apply BR_BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq9 Hss'].
    apply BB_BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    destruct Hss' as [eq10 Hss'].
    apply BN_correct in Hss';
      [ | reason_bounds s_bound | reason_bounds s'_bound ].
    apply state_ext.
    + apply hash_Player_inj; auto.
    + apply mp_of_board_eq.
      intros [] []; auto.
    + do 2 rewrite mp_of_board_King in eq2.
      inversion eq2; auto.
    + do 2 rewrite mp_of_board_King in eq3.
      inversion eq3; auto.
  - apply hash_Player_small.
  - apply hash_Player_small.
  - apply hash_mp_bound with (m := m); auto.
  - apply hash_mp_bound with (m := m); auto.
Qed.
