Require Import List.
Import ListNotations.

Require Import Games.Util.Dec.

Require Import Games.Game.Player.
Require Import Chess.Chess.

Require Import Chess.TB.Material.

Definition material_positions : Type :=
  Player -> Piece -> list Pos.

Definition empty_mp : material_positions :=
  fun _ _ => [].

Definition mp_add_pos : Player -> Piece -> Pos -> material_positions ->
  material_positions :=
  fun c p pos mp =>
    fun c' p' =>
      match eq_dec (c', p') (c, p) with
      | left _ => pos :: mp c' p'
      | right _ => mp c' p'
      end.

Fixpoint indices {n} : Vec.Vec (Fin.Fin n) n :=
  match n with
  | 0 => tt
  | S m => (inl tt, Vec.vmap (inr : Fin.Fin m -> Fin.Fin (S m)) indices)
  end.

Definition with_indices {X} {n} (v : Vec.Vec X n) :
  Vec.Vec (Fin.Fin n * X) n :=
  Vec.vzip pair indices v.

Definition with_coords {X} {m n} (M : Mat.Mat X m n) :
  Mat.Mat (Fin.Fin m * (Fin.Fin n * X)) m n :=
  Vec.vzip (fun i v => Vec.vmap (fun p => (i, p)) v)
    indices
    (Vec.vmap with_indices M).

Fixpoint mp_of_indcol {k} : Vec.Vec (Fin.Fin 8 (*m*) *
  (Fin.Fin 8 (*n*) * option (Player * Piece))) k ->
  material_positions :=
  match k with
  | 0 => fun _ => empty_mp
  | S k' => fun v =>
    match v with
    | ((i, (j, Some (c, p))), v') =>
      mp_add_pos c p (i, j) (mp_of_indcol v')
    | ((_, (_, None)), v') => mp_of_indcol v'
    end
  end.

Definition mp_app (m1 m2 : material_positions) : material_positions :=
  fun c p => m1 c p ++ m2 c p.

Fixpoint mp_concat {n} : Vec.Vec material_positions n -> 
  material_positions :=
  match n with
  | 0 => fun _ => empty_mp
  | S m => fun v => mp_app (fst v) (mp_concat (snd v))
  end.

Definition mp_of_board (b : Board) : material_positions :=
  mp_concat (Vec.vmap mp_of_indcol (with_coords b)).

Lemma mp_of_board_NoDup b : forall c p,
  NoDup (mp_of_board b c p).
Admitted.

Lemma mp_of_board_correct1 (b : Board) : forall c p x,
  Mat.maccess x b = Some (c, p) -> In x (mp_of_board b c p).
Admitted.

Lemma mp_of_board_correct2 (b : Board) : forall c p x,
  In x (mp_of_board b c p) -> Mat.maccess x b = Some (c, p).
Admitted.

Lemma mp_of_board_eq : forall b b',
  (forall c p, mp_of_board b c p = mp_of_board b' c p) -> b = b'.
Proof.
  intros b b' Hbb'.
  apply Mat.mat_ext.
  intro x.
  destruct (Mat.maccess x b) as [[c p]|] eqn:pf.
  - apply mp_of_board_correct1 in pf.
    rewrite Hbb' in pf.
    apply mp_of_board_correct2 in pf.
    congruence.
  - destruct (Mat.maccess x b') as [[c p]|] eqn:pf'; auto.
    apply mp_of_board_correct1 in pf'.
    rewrite <- Hbb' in pf'.
    apply mp_of_board_correct2 in pf'.
    congruence.
Qed.

Lemma singleton_lemma {X} (x : X) l :
  In x l ->
  (forall x', In x' l -> x' = x) ->
  NoDup l ->
  l = [x].
Proof.
  intros pf1 pf2 pf3.
  destruct l as [|y [|y' l']].
  - destruct pf1.
  - rewrite (pf2 y); auto.
    now left.
  - rewrite (pf2 y) in pf3; [|now left].
    rewrite (pf2 y') in pf3; [|right; now left].
    inversion pf3.
    elim H1; now left.
Qed.

Lemma mp_of_board_King : forall c s,
  mp_of_board (board s) c King = [king s c].
Proof.
  intros [] s.
  - apply singleton_lemma.
    + apply mp_of_board_correct1.
      apply s.
    + intros p Hp.
      apply mp_of_board_correct2 in Hp.
      apply kings_unique in Hp; auto.
    + apply mp_of_board_NoDup.
  - apply singleton_lemma.
    + apply mp_of_board_correct1.
      apply s.
    + intros p Hp.
      apply mp_of_board_correct2 in Hp.
      apply kings_unique in Hp; auto.
    + apply mp_of_board_NoDup.
Qed.

Lemma length_mp_concat {n} (ms : Vec.Vec material_positions n) :
  forall c p,
    length (mp_concat ms c p) =
    Vec_sum (Vec.vmap (fun m => length (m c p)) ms).
Proof.
  induction n.
  - intros; reflexivity.
  - intros c p; simpl.
    rewrite <- IHn.
    unfold mp_app.
    rewrite app_length; auto.
Qed.

Require Import Chess.Util.MatAction.

Lemma vaccess_indices {n} (i : Fin.Fin n) :
  Vec.vaccess i indices = i.
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + simpl.
      rewrite vaccess_vmap.
      rewrite IHn; auto.
Qed.

Lemma length_mp_add_cons c c' p p' x m :
  length (mp_add_pos c' p' x m c p) =
  match eq_dec (c,p) (c',p') with
  | left _ => S (length (m c p))
  | right _ => length (m c p)
  end.
Proof.
  unfold mp_add_pos.
  destruct eq_dec; auto.
Qed.

Lemma eq_dec_Some {X Y} `{Discrete X} (x x' : X) (y y' : Y) :
  match eq_dec (Some x) (Some x') with
  | left _ => y
  | right _ => y'
  end =
  match eq_dec x x' with
  | left _ => y
  | right _ => y'
  end.
Proof.
  destruct (eq_dec (Some x) (Some x')), (eq_dec x x').
  + auto.
  + inversion e; contradiction.
  + subst; contradiction.
  + auto.
Qed.

Lemma eq_dec_Some_None {X Y} `{Discrete X} (x : X) (y y' : Y) :
  match eq_dec (Some x) None with
  | left _ => y
  | right _ => y'
  end = y'.
Proof.
  destruct eq_dec.
  - discriminate.
  - auto.
Qed.

Lemma mp_of_indcol_count {k} c p (v : Vec.Vec (Fin.Fin 8 * (Fin.Fin 8 *
  option (Player * Piece))) k) :
  length (mp_of_indcol v c p) =
  Vec_count (Some (c, p)) (Vec.vmap (fun p => snd (snd p)) v).
Proof.
  induction k.
  - auto.
  - destruct v as [hd v'].
    destruct hd as [i [j o]].
    destruct o as [[c' p']|].
    + simpl mp_of_indcol.
      rewrite vmap_cons.
      simpl snd.
      rewrite Vec_count_cons.
      rewrite <- IHk.
      rewrite length_mp_add_cons.
      rewrite eq_dec_Some; auto.
    + simpl mp_of_indcol.
      rewrite vmap_cons.
      simpl snd.
      rewrite Vec_count_cons.
      rewrite <- IHk.
      rewrite eq_dec_Some_None; auto.
Qed.

Lemma mp_of_board_count b c p :
  length (mp_of_board b c p) =
  count c p b.
Proof.
  unfold count.
  unfold Mat_count.
  unfold mp_of_board.
  rewrite length_mp_concat.
  rewrite Vec.vmap_vmap.
  f_equal.
  apply Vec.vec_ext.
  intro i.
  repeat rewrite vaccess_vmap.
  rewrite mp_of_indcol_count.
  unfold with_coords.
  rewrite vaccess_vzip.
  rewrite vaccess_vmap.
  rewrite vaccess_indices.
  rewrite Vec.vmap_vmap.
  simpl snd.
  unfold with_indices.
  f_equal.
  apply Vec.vec_ext.
  intro j.
  rewrite vaccess_vmap.
  rewrite vaccess_vzip.
  auto.
Qed.

Lemma king_count : forall c s,
  count c King (board s) = 1.
Proof.
  intros.
  rewrite <- mp_of_board_count.
  rewrite mp_of_board_King; auto.
Qed.
