Require Import Lia.
Require Import List.

Require Import Games.Game.Game.
Require Import Games.Game.Player.
Require Import Games.Game.Strategy.

Inductive win {G : Game} (p : Player) : GameState G -> Type :=
  | atom_win : forall b,
      atomic_res b = Some (Win p) ->
      win p b
  | eloise_win : forall b,
      atomic_res b = None ->
      to_play b = p ->
      forall m, win p (exec_move b m) ->
      win p b
  | abelard_win : forall b,
      atomic_res b = None ->
      to_play b = opp p ->
      (forall m, win p (exec_move b m)) ->
      win p b.

Arguments atom_win {_} {_} {_} _.
Arguments eloise_win {_} {_} {_} _ _ _ _.
Arguments abelard_win {_} {_} {_} _ _ _.

Fixpoint depth {G} {p} {s : GameState G} (w : win p s) : nat :=
  match w with
  | atom_win _ => 0
  | eloise_win _ _ _ w' => S (depth w')
  | @abelard_win _ _ s _ _ ws => S (list_max
      (map (fun m => depth (ws m)) (enum_moves s)))
  end.

Lemma list_max_ne_achieves (xs : list nat) :
  {xs = nil} + {In (list_max xs) xs}.
Proof.
  induction xs.
  - now left.
  - right.
    simpl.
    destruct IHxs.
    + left.
      rewrite e.
      symmetry; apply PeanoNat.Nat.max_0_r.
    + destruct (PeanoNat.Nat.max_spec_le a (list_max xs))
        as [[_ Hle]|[_ Hle]];
      rewrite Hle; tauto.
Defined.

Definition minimal {G} {p} {s : GameState G} (w : win p s) : Prop :=
  forall (w' : win p s), depth w <= depth w'.

Fixpoint saturated {G} {p} {s : GameState G} (w : win p s) : Prop :=
  match w with
  | atom_win _ => True
  | @eloise_win _ _ s' _ _ _ w' => saturated w' /\
      forall (m' : Move s') (w'' : win p (exec_move s' m')), depth w' <= depth w''
  | abelard_win _ _ ws => forall m, saturated (ws m)
  end.

Lemma sat_lower {G} {p} {s : GameState G} : forall (w : win p s)
  (n : nat), saturated w -> n <= depth w -> exists (s' : GameState G) (w' : win p s'), depth w' = n /\ saturated w'.
Proof.
  induction w; intros n w_s n_le.
  - exists b, (atom_win e).
    simpl in *; lia.
  - simpl in n_le.
    rewrite PeanoNat.Nat.le_succ_r in n_le.
    destruct n_le.
    + simpl in w_s; now apply IHw.
    + rewrite H.
      exists _, (eloise_win e e0 m w); split.
      * reflexivity.
      * exact w_s.
  - simpl in n_le.
    rewrite PeanoNat.Nat.le_succ_r in n_le.
    destruct n_le.
    + assert (exists m : Move b,
        n <= depth (w m)) as [m Hm].
      { destruct (list_max_ne_achieves (map (fun m : Move b => depth (w m))
          (enum_moves b))).
        * pose (map_eq_nil _ _ e1).
          destruct (nil_atomic_res e2); congruence.
        * rewrite in_map_iff in i.
          destruct i as [m' Hm'].
          exists m'; lia.
      }
      exact (H m n (w_s m) Hm).
    + rewrite H0.
      exists _, (abelard_win e e0 w); now split.
Qed.

Lemma list_max_map {X} (f g : X -> nat) (fg : forall x, f x <= g x)
  (xs : list X) : list_max (map f xs) <= list_max (map g xs).
Proof.
  induction xs; simpl.
  - lia.
  - simpl.
    apply PeanoNat.Nat.max_le_compat.
    + apply fg.
    + exact IHxs.
Qed.

Lemma saturated_minimal {G} {p} {s : GameState G} (w : win p s) :
  saturated w -> minimal w.
Proof.
  induction w; unfold minimal; simpl; intros.
  - lia.
  - destruct w'.
    + congruence.
    + simpl.
      destruct H.
      pose (H0 m0 w').
      now apply le_n_S.
    + elim (opp_no_fp p); congruence.
  - destruct w'.
    + congruence.
    + elim (opp_no_fp p); congruence.
    + simpl.
      apply le_n_S.
      apply list_max_map.
      intro; now apply H.
Qed.

Definition mate {G} (p : Player) (s : GameState G) (n : nat) : Type :=
  { w : win p s & depth w = n /\ minimal w }.

Fixpoint strategy_of_win {G : Game} {p : Player} {s : GameState G}
  (w : win p s) : strategy p s :=
  match w with
  | atom_win res_pf =>
      atom_strategy res_pf
  | eloise_win _ play_pf m w =>
      eloise_strategy play_pf m (strategy_of_win w)
  | abelard_win _ play_pf ws =>
      abelard_strategy play_pf (fun m =>
        strategy_of_win (ws m))
  end.

Lemma strategy_of_win_correct {G : Game} {p : Player} (s : GameState G)
  (w : win p s) : winning_strategy p (strategy_of_win w).
Proof.
  induction w; constructor; auto.
Qed.

Lemma unique_winner {G} : forall p p' (b : GameState G),
  win p b -> win p' b -> p = p'.
Proof.
  intros p p' b w; induction w; intro w'.
  - destruct w'; congruence.
  - destruct w'; try congruence; auto.
  - destruct w'; try congruence.
    + apply (H m); exact w'.
    + apply opp_inj; congruence.
Qed.

Inductive forces {G : Game} (p : Player) (P : GameState G -> Prop)
  : GameState G -> Type :=
  | atom_force : forall b, P b -> forces p P b
  | eloise_force : forall b, to_play b = p ->
      atomic_res b = None ->
      forall m, forces p P (exec_move b m) ->
      forces p P b
  | abelard_force : forall b, to_play b = opp p ->
      atomic_res b = None ->
      (forall m, forces p P (exec_move b m)) ->
      forces p P b.

Definition awin {G} : Player -> GameState G -> Prop :=
  fun p b => atomic_res b = Some (Win p).

Definition forces_win {G : Game} (p : Player) (b : GameState G)
  : forces p (awin p) b -> win p b.
Proof.
  intro bf.
  induction bf.
  - apply atom_win; auto.
  - eapply eloise_win; eauto.
  - apply abelard_win; auto.
Defined.

Definition pforces {G : Game} (p : Player) (P Q : GameState G -> Prop) : Type :=
  forall b, P b -> forces p Q b.

Definition pforces_win {G : Game} : forall p (P : GameState G -> Prop),
  pforces p P (awin p) -> forall b, P b -> win p b.
Proof.
  intros.
  apply forces_win.
  apply X.
  auto.
Defined.

Definition pforces_trans {G} (p : Player) : forall (P Q R : GameState G -> Prop),
  pforces p P Q -> pforces p Q R -> pforces p P R.
Proof.
  intros P Q R fPQ fQR b Hb.
  pose proof (fPQ b Hb) as bfQ.
  clear fPQ.
  clear Hb.
  induction bfQ.
  - apply fQR; exact p0.
  - eapply eloise_force; auto.
    eapply IHbfQ.
  - eapply abelard_force; auto.
Defined.

Section Measure.

Context {G : Game}.

Variable M : nat -> GameState G -> Prop.

Variable winner : Player.

Variable M_decr : forall n, pforces winner (M (S n)) (M n).

Definition M_ind : forall n, pforces winner (M n) (M 0).
Proof.
  intro n.
  induction n.
  - intros b Hb.
    apply atom_force.
    exact Hb.
  - eapply pforces_trans.
    + apply M_decr.
    + exact IHn.
Defined.

End Measure.
