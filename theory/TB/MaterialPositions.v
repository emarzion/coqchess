Require Import List.
Import ListNotations.

Require Import Games.Util.Dec.

Require Import Games.Game.Player.
Require Import Chess.Chess.

Require Import Chess.TB.Material.

Require Import Chess.Util.MatAction.

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

Lemma In_mp_app_left m1 m2 c p x :
  In x (m1 c p) ->
  In x (mp_app m1 m2 c p).
Proof.
  intro pf.
  apply in_or_app; now left.
Qed.

Lemma In_mp_app_right m1 m2 c p x :
  In x (m2 c p) ->
  In x (mp_app m1 m2 c p).
Proof.
  intro pf.
  apply in_or_app; now right.
Qed.

Lemma In_mp_app_inv m1 m2 c p x :
  In x (mp_app m1 m2 c p) ->
  In x (m1 c p) \/ In x (m2 c p).
Proof.
  intro; apply in_app_or; auto.
Qed.

Fixpoint mp_concat {n} : Vec.Vec material_positions n -> 
  material_positions :=
  match n with
  | 0 => fun _ => empty_mp
  | S m => fun v => mp_app (fst v) (mp_concat (snd v))
  end.

Definition mp_of_board (b : Board) : material_positions :=
  mp_concat (Vec.vmap mp_of_indcol (with_coords b)).

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

Lemma In_mp_concat1 {n} c p x (v : Vec.Vec material_positions n) :
  forall i,
    In x (Vec.vaccess i v c p) ->
    In x (mp_concat v c p).
Proof.
  induction n; intros i pf.
  - destruct i.
  - destruct i as [[]|j].
    + simpl in *.
      apply In_mp_app_left; auto.
    + apply IHn in pf.
      simpl; apply In_mp_app_right; auto.
Qed.

Lemma In_mp_concat2 {n} c p x (v : Vec.Vec material_positions n) :
  In x (mp_concat v c p) ->
  exists i, In x (Vec.vaccess i v c p).
Proof.
  induction n; intros pf.
  - destruct pf.
  - simpl in pf.
    apply In_mp_app_inv in pf.
    destruct pf as [pf1|pf2].
    + exists (inl tt); auto.
    + apply IHn in pf2.
      destruct pf2 as [i Hi].
      exists (inr i); auto.
Qed.

Lemma NoDup_mp_concat {n} c p (v : Vec.Vec material_positions n) :
  (forall i, NoDup (Vec.vaccess i v c p)) ->
  (forall i j x, In x (Vec.vaccess i v c p) -> In x (Vec.vaccess j v c p) -> i = j) ->
  NoDup (mp_concat v c p).
Proof.
  induction n; intros cmp_nd pw_disj.
  - simpl; constructor.
  - simpl.
    apply TB.NoDup_app.
    + apply (cmp_nd (inl tt)).
    + apply IHn.
      * intro i; apply (cmp_nd (inr i)).
      * intros i j x pfi pfj.
        pose proof (pw_disj (inr i) (inr j) x pfi pfj).
        congruence.
    + intros x pf1 pf2.
      apply In_mp_concat2 in pf2.
      destruct pf2 as [i Hi].
      pose proof (pw_disj (inl tt) (inr i) x pf1 Hi).
      discriminate.
Qed.

Lemma eq_dec_refl {X Y} `{Discrete X} (x : X) (y y' : Y) :
  match eq_dec x x with
  | left _ => y
  | right _ => y'
  end = y.
Proof.
  destruct eq_dec.
  - auto.
  - contradiction.
Qed.

Lemma In_mp_add_pos_left c p x m :
  In x (mp_add_pos c p x m c p).
Proof.
  unfold mp_add_pos.
  rewrite eq_dec_refl.
  now left.
Qed.

Lemma In_mp_add_pos_right c c' p p' x x' m :
  In x (m c p) ->
  In x (mp_add_pos c' p' x' m c p).
Proof.
  intro pf.
  unfold mp_add_pos; destruct eq_dec.
  - now right.
  - auto.
Qed.

Lemma In_mp_add_pos_inv c c' p p' x x' m :
  In x (mp_add_pos c' p' x' m c p) ->
  (x = x' /\ c = c' /\ p = p') \/ In x (m c p).
Proof.
  unfold mp_add_pos.
  destruct eq_dec; intro pf.
  - destruct pf.
    + left; inversion e; firstorder.
    + right; auto.
  - now right.
Qed.

Lemma mp_of_indcol_In {n} (v: Vec.Vec (Fin.Fin 8 * (Fin.Fin 8 * option (Player * Piece))) n) : forall i j c p k,
  Vec.vaccess k v = (i, (j, (Some (c, p)))) ->
  In (i, j) (mp_of_indcol v c p).
Proof.
  intros i j c p k pf.
  induction n.
  - destruct k.
  - destruct k as [[]|k'].
    + destruct v as [hd v'].
      simpl in pf.
      rewrite pf; simpl.
      apply In_mp_add_pos_left.
    + destruct v as [[i' [j' o]] v'].
      destruct o as [[c' p']|]; simpl in pf; simpl.
      * apply IHn in pf.
        apply In_mp_add_pos_right; auto.
      * apply IHn in pf; auto.
Qed.

Lemma In_mp_of_indcol_inv {n} (v : Vec.Vec (Fin.Fin 8 *
  (Fin.Fin 8 * option (Player * Piece))) n) i j c p :
  In (i, j) (mp_of_indcol v c p) ->
  exists k : Fin.Fin n,
    Vec.vaccess k v = (i, (j, Some (c, p))).
Proof.
  induction n; intro pf.
  - destruct pf.
  - destruct v as [hd v'].
    destruct hd as [i' [j' o]].
    destruct o as [[c' p']|].
    + simpl in pf.
      apply In_mp_add_pos_inv in pf.
      destruct pf as [pf|pf].
      * exists (inl tt).
        destruct pf as [pf1 [pf2 pf3]].
        simpl.
        inversion pf1; subst; auto.
      * apply IHn in pf.
        destruct pf as [k Hk].
        exists (inr k); auto.
    + simpl in pf.
      apply IHn in pf.
      destruct pf as [k Hk].
      exists (inr k); auto.
Qed.

Lemma to_list_cons {X} {n} (x : X) (v : Vec.Vec X n) :
  Vec.to_list ((x, v) : Vec.Vec X (S n)) = x :: Vec.to_list v.
Proof.
  reflexivity.
Qed.

Lemma In_to_list {X} {n} (x : X) (i : Fin.Fin n)
  (v : Vec.Vec X n) :
  Vec.vaccess i v = x ->
  In x (Vec.to_list v).
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i as [[]|j].
    + now left.
    + right; apply (IHn j); auto.
Qed.

Lemma mp_of_indcol_NoDup {n} (v : Vec.Vec (Fin.Fin 8 *
  (Fin.Fin 8 * option (Player * Piece))) n) c p :
  NoDup (Vec.to_list (Vec.vmap (fun x => fst (snd x)) v)) ->
  NoDup (mp_of_indcol v c p).
Proof.
  induction n; intro pf.
  - constructor.
  - destruct v as [hd v'].
    destruct hd as [i [j o]].
    simpl; destruct o as [[c' p']|].
    + unfold mp_add_pos.
      destruct eq_dec.
      * constructor.
        -- intro pf'.
           rewrite vmap_cons in pf.
           simpl fst in pf; simpl snd in pf.
           rewrite to_list_cons in pf.
           rewrite NoDup_cons_iff in pf.
           destruct pf as [pf1 pf2].
           apply pf1.
           apply In_mp_of_indcol_inv in pf'.
           destruct pf' as [k Hk].
           apply In_to_list with (i := k).
           rewrite vaccess_vmap.
           rewrite Hk; auto.
        -- inversion pf; auto.
      * apply IHn.
        inversion pf; auto.
    + apply IHn.
      inversion pf; auto.
Qed.

Lemma to_list_vmap {X Y} {n} (f : X -> Y) (v : Vec.Vec  X n) :
  Vec.to_list (Vec.vmap f v) = List.map f (Vec.to_list v).
Proof.
  induction n.
  - auto.
  - simpl; rewrite IHn; auto.
Qed.

Lemma to_list_vzip_pair {X Y} {n} (v1 : Vec.Vec X n)
  (v2 : Vec.Vec Y n) :
  Vec.to_list (Vec.vzip pair v1 v2) =
  combine (Vec.to_list v1) (Vec.to_list v2).
Proof.
  induction n.
  - auto.
  - destruct v1 as [x1 w1].
    destruct v2 as [x2 w2].
    simpl; rewrite IHn; auto.
Qed.

Lemma map_fst_combine {X Y} (l1 : list X) : forall (l2 : list Y),
  length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  induction l1; intros l2 pf.
  - reflexivity.
  - destruct l2.
    + discriminate.
    + simpl; rewrite IHl1; auto.
Qed.

Lemma length_to_list {X} {n} (v : Vec.Vec X n) :
  length (Vec.to_list v) = n.
Proof.
  induction n.
  - auto.
  - simpl; rewrite IHn; auto.
Qed.

Lemma to_list_indices {n} :
  Vec.to_list (@indices n) = Fin.all_fin n.
Proof.
  induction n.
  - auto.
  - simpl.
    rewrite to_list_vmap.
    rewrite IHn; auto.
Qed.

Lemma NoDup_map_inj {X Y} (f : X -> Y) (xs : list X)
  (f_inj : forall x x', f x = f x' -> x = x') :
  NoDup xs -> NoDup (map f xs).
Proof.  
  induction xs; intro nd.
  - constructor.
  - simpl; constructor.
    + intro pf.
      rewrite in_map_iff in pf.
      destruct pf as [x [Hx1 Hx2]].
      apply f_inj in Hx1; subst.
      inversion nd; contradiction.
    + apply IHxs.
      inversion nd; auto.
Qed.

Lemma all_fin_NoDup {n} :
  NoDup (Fin.all_fin n).
Proof.
  induction n.
  - constructor.
  - simpl; constructor.
    + intro pf.
      rewrite in_map_iff in pf.
      destruct pf as [i [Hi _]].
      discriminate.
    + apply NoDup_map_inj.
      * intros; congruence.
      * auto.
Qed.

Lemma mp_of_board_NoDup b : forall c p,
  NoDup (mp_of_board b c p).
Proof.
  intros c p.
  apply NoDup_mp_concat.
  - intro i.
    rewrite vaccess_vmap.
    unfold with_coords.
    rewrite vaccess_vzip.
    rewrite vaccess_vmap.
    unfold with_indices.
    rewrite vaccess_indices.
    apply mp_of_indcol_NoDup.
    rewrite Vec.vmap_vmap.
    simpl snd.
    rewrite to_list_vmap.
    rewrite to_list_vzip_pair.
    rewrite map_fst_combine.
    + rewrite to_list_indices.
      apply all_fin_NoDup.
    + do 2 rewrite length_to_list; auto.
  - intros i j [i' j'] pf1 pf2.
    rewrite vaccess_vmap in *.
    apply In_mp_of_indcol_inv in pf1, pf2.
    destruct pf1 as [k Hk].
    destruct pf2 as [k' Hk'].
    unfold with_coords in *.
    rewrite vaccess_vzip in *.
    repeat rewrite vaccess_vmap in *.
    rewrite vaccess_indices in *.
    congruence.
Qed.

Lemma mp_of_board_correct1 (b : Board) : forall c p x,
  Mat.maccess x b = Some (c, p) -> In x (mp_of_board b c p).
Proof.
  intros c p [i j] pf.
  apply In_mp_concat1 with (i := i).
  rewrite vaccess_vmap.
  unfold with_coords.
  rewrite vaccess_vzip.
  rewrite vaccess_indices.
  rewrite vaccess_vmap.
  apply mp_of_indcol_In with (k := j).
  rewrite vaccess_vmap.
  unfold with_indices.
  rewrite vaccess_vzip.
  rewrite vaccess_indices.
  repeat f_equal; auto.
Qed.

Lemma mp_of_board_correct2 (b : Board) : forall c p x,
  In x (mp_of_board b c p) -> Mat.maccess x b = Some (c, p).
Proof.
  intros c p [i j] pf.
  unfold mp_of_board in pf.
  apply In_mp_concat2 in pf.
  destruct pf as [k Hk].
  rewrite vaccess_vmap in Hk.
  apply In_mp_of_indcol_inv in Hk.
  destruct Hk as [k' Hk'].
  unfold with_coords in Hk'.
  rewrite vaccess_vzip in Hk'.
  do 2 rewrite vaccess_vmap in Hk'.
  unfold with_indices in Hk'.
  rewrite vaccess_vzip in Hk'.
  do 2 rewrite vaccess_indices in Hk'.
  unfold Mat.maccess.
  simpl fst; simpl snd.
  congruence.
Qed. (*?*)

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
