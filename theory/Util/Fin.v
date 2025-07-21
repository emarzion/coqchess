Require Import Coq.Arith.PeanoNat.
Require Import List.
Import ListNotations.
Require Import Lia.

Require Import Chess.Util.Dist.
Require Import Chess.Util.SBetween.
Require Import Chess.Util.Dec.
Require Import Chess.Util.UIP.
Require Import Games.Util.Dec.

Fixpoint Fin n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint Fin_of_nat {m} (n : nat) : Fin (n + S m) :=
  match n with
  | 0 => inl tt
  | S k => inr (Fin_of_nat k)
  end.

Fixpoint val {n} : Fin n -> nat :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => 0
    | inr j => S (val j)
    end
  end.

Lemma val_inj : forall {n} (i j : Fin n),
  val i = val j -> i = j.
Proof.
  induction n; intros.
  { destruct i. }
  { destruct i as [[]|i'];
    destruct j as [[]|j'].
    { reflexivity. }
    { discriminate. }
    { discriminate. }
    { rewrite (IHn i' j').
      { reflexivity. }
      { now inversion H. }
    }
  }
Qed.

Fixpoint all_fin n : list (Fin n) :=
  match n with
  | 0 => []
  | S m => inl tt :: map inr (all_fin m)
  end.

Lemma all_fin_In (n : nat) : forall i : Fin n,
  In i (all_fin n).
Proof.
  induction n.
  - intros [].
  - intros [[]|j].
    + left; reflexivity.
    + right.
      apply in_map.
      apply IHn.
Qed.

Definition fin_dist {n} : Fin n -> Fin n -> nat :=
  fun i j => dist (val i) (val j).

Lemma fin_dist_sym {n} : forall i j : Fin n,
  fin_dist i j = fin_dist j i.
Proof.
  intros.
  apply dist_sym.
Qed.

Definition fin_sbetween {n} : Fin n -> Fin n -> Fin n -> Prop :=
  fun i j k => sbetween (val i) (val j) (val k).

Lemma fin_sbetween_sym {n} : forall i j k : Fin n,
  fin_sbetween i j k -> fin_sbetween k j i.
Proof.
  intros i j k; unfold fin_sbetween; apply sbetween_sym.
Qed.

#[export] Instance Fin_Discrete : forall {n},
  Discrete (Fin n).
Proof.
  intros.
  constructor.
  intros i j.
  destruct (Nat.eq_dec (val i) (val j)).
  - left; apply val_inj; auto.
  - right; congruence.
Defined.

Global Instance Fin_Exhaustible : forall {n},
  Exhaustible (Fin n).
Proof.
  intro n.
  constructor.
  induction n.
  - intros P _.
    right; intros [[] _].
  - intros P Pd.
    destruct (Pd (inl tt)).
    + left; exists (inl tt); easy.
    + destruct (IHn (fun i => P (inr i)) (fun i => Pd (inr i))).
      * left. destruct e as [i Hi].
        exists (inr i); exact Hi.
      * right; intros [i Hi].
        destruct i as [[]|j].
        ** exact (n0 Hi).
        ** apply n1.
           exists j.
           exact Hi.
Defined.

Fixpoint next {n} {struct n} : Fin n -> option (Fin n) :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ =>
      match m with
      | 0 => None
      | S p => Some (inr (inl tt))
      end
    | inr j =>
      match next j with
      | Some k => Some (inr k)
      | None => None
      end
    end
  end.

Fixpoint prev {n} {struct n } : Fin n -> option (Fin n) :=
  match n with
  | 0 => fun e =>
    match e with
    end
  | S m => fun i =>
    match i with
    | inl _ => None
    | inr j =>
      match prev j with
      | Some k => Some (inr k)
      | None => Some (inl tt)
      end
    end
  end.

Lemma prev_next {n} : forall i j : Fin n,
  next i = Some j ->
  prev j = Some i.
Proof.
  induction n; intros i j Hij.
  - destruct i.
  - simpl in *.
    destruct i as [[]|i'].
    + destruct j as [|j'].
      * destruct n; discriminate.
      * destruct n; try discriminate.
        inversion Hij; auto.
    + destruct (next i') eqn:Hi'; try discriminate.
      inversion Hij.
      rewrite (IHn i'); auto.
Qed.

Lemma next_prev {n} : forall i j : Fin n,
  prev i = Some j ->
  next j = Some i.
Proof.
  induction n; intros i j Hij.
  - destruct i.
  - simpl in *.
    destruct i as [|i']; try discriminate.
    destruct (prev i') eqn:Hi'.
    + inversion Hij.
      rewrite (IHn i'); auto.
    + inversion Hij.
      destruct n.
      * destruct i'.
      * destruct i' as [[]|]; auto.
        simpl in Hi'.
        destruct (prev f); discriminate.
Qed.

Definition Fin_lt {n} : Fin n -> Fin n -> Prop :=
  fun i j => val i < val j.

Definition Fin_gt {n} : Fin n -> Fin n ->
Prop :=
  fun i j => val i > val j.

Lemma Fin_lt_inl {n} u :
  Acc (@Fin_lt (S n)) (inl u).
Proof.
  destruct u.
  constructor.
  intros j Hij.
  unfold Fin_lt in Hij; simpl in Hij; lia.
Defined.

Fixpoint Fin_lt_inr {n} (i : Fin n)
  (a : Acc (@Fin_lt n) i) {struct a} :
  Acc (@Fin_lt (S n)) (inr i).
Proof.
  destruct a as [Hi].
  constructor.
  intros j Hij.
  destruct j as [[]|j'].
  - apply Fin_lt_inl.
  - apply Fin_lt_inr.
    apply Hi.
    unfold Fin_lt in Hij.
    unfold Fin_lt.
    simpl in *; lia.
Defined.

Lemma Fin_lt_wf {n} :
  well_founded (@Fin_lt n).
Proof.
  induction n; intro i.
  - destruct i.
  - destruct i.
    + apply Fin_lt_inl.
    + apply Fin_lt_inr.
      apply IHn.
Defined.

Fixpoint Fin_gt_inr {n} (i : Fin n)
  (a : Acc (@Fin_gt n) i) {struct a} :
  Acc (@Fin_gt (S n)) (inr i).
Proof.
  destruct a as [Hi].
  constructor.
  intros j Hij.
  destruct j as [[]|j'].
  - unfold Fin_gt in Hij.
    simpl in Hij; lia.
  - apply Fin_gt_inr.
    apply Hi.
    unfold Fin_gt in Hij.
    unfold Fin_gt.
    simpl in *; lia.
Defined.

Lemma Fin_gt_wf {n} :
  well_founded (@Fin_gt n).
Proof.
  induction n; intro i.
  - destruct i.
  - destruct i.
    + constructor.
      intros j Hij.
      destruct j.
      * unfold Fin_gt in Hij.
        simpl in Hij.
        destruct u,u0; lia.
      * apply Fin_gt_inr.
        apply IHn.
    + apply Fin_gt_inr.
      apply IHn.
Defined.

Definition fin_eqb {n} : Fin n -> Fin n -> bool :=
  fun i j =>
    match eq_dec i j with
    | left _ => true
    | right _ => false
    end.

Lemma fin_eqb_iff {n} : forall i j : Fin n,
  fin_eqb i j = true <-> i = j.
Proof.
  unfold fin_eqb.
  intros i j; split; intro pf.
  - destruct (eq_dec i j); auto.
    discriminate.
  - destruct (eq_dec i j); auto.
Qed.

Lemma next_gt {n} (i j : Fin n) :
  next i = Some j ->
  Fin_gt j i.
Proof.
  unfold Fin_gt.
  induction n; intro Hi.
  - destruct i.
  - simpl in Hi.
    destruct i as [|i']; simpl.
    + destruct n; inversion Hi.
      lia.
    + destruct j as [|j'];
      destruct (next i') eqn:Hi';
      inversion Hi; subst.
      apply IHn in Hi'; lia.
Qed.

Fixpoint get_all_above_aux {n} (i : Fin n) (a :
  Acc (@Fin_gt n) i) {struct a} : list (Fin n).
Proof.
  destruct (next i) as [j|] eqn:Hij.
  - apply (cons i).
    apply (get_all_above_aux n j).
    destruct a as [Hi].
    apply Hi.
    now apply next_gt.
  - exact [i].
Defined.

Definition get_all_above {n} (i : Fin n) : list (Fin n) :=
  get_all_above_aux i (Fin_gt_wf i).

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

Lemma front_inr {n} (i : Fin (S n)) :
  front (inr i : Fin (S (S n))) = inr (front i).
Proof.
  reflexivity.
Qed.

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

Fixpoint Fin_rev {n} : Fin.Fin n -> Fin.Fin n :=
  match n with
  | 0 => fun i => i
  | S m => fun i =>
    match i with
    | inl _ => last
    | inr j => front (Fin_rev j)
    end
  end.

Lemma Fin_rev_inr {n} (i : Fin n) :
  Fin_rev (inr i : Fin (S n)) = front (Fin_rev i).
Proof.
  reflexivity.
Qed.

Lemma Fin_rev_last {n} :
  Fin_rev (last : Fin (S n)) = inl tt.
Proof.
  induction n.
  - reflexivity.
  - simpl last.
    rewrite @Fin_rev_inr.
    rewrite IHn.
    reflexivity.
Qed.

Lemma Fin_rev_front {n} (i : Fin n) :
  Fin_rev (front i) = inr (Fin_rev i).
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + rewrite Fin_rev_inr.
      destruct n.
      * destruct j.
      * rewrite front_inr.
        rewrite Fin_rev_inr.
        rewrite IHn.
        reflexivity.
Qed.

Lemma Fin_rev_Fin_rev {n} (i : Fin.Fin n) :
  Fin_rev (Fin_rev i) = i.
Proof.
  induction n.
  - reflexivity.
  - unfold Fin_rev at 2.
    destruct i.
    + destruct u; apply Fin_rev_last.
    + rewrite Fin_rev_front.
      rewrite IHn; auto.
Qed.

Lemma Fin_rev_inl {n} :
  Fin_rev (inl tt : Fin (S n)) = last.
Proof.
  rewrite <- (Fin_rev_Fin_rev last).
  rewrite Fin_rev_last; auto.
Qed.

Lemma val_inr {n} (i : Fin.Fin n) : Fin.val (inr i : Fin.Fin (S n)) = S (Fin.val i).
Proof.
  reflexivity.
Qed.

Lemma val_bound {n} (i : Fin.Fin n) :
  Fin.val i < n.
Proof.
  induction n.
  - destruct i.
  - destruct i as [|j].
    + simpl.
      apply PeanoNat.Nat.lt_0_succ.
    + rewrite val_inr.
      apply Arith_base.lt_n_S_stt.
      apply IHn.
Qed.
