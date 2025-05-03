Require Import Arith.
Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Games.Game.Player.

Require Import Chess.Chess.Chess.

Require Import Games.Util.Dec.

Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.ListUtil.

Definition all_pieces (s : ChessState) : list (Player * Piece) :=
  filter_Some (Mat.to_list (board s)).

Definition eqb {X} `{Discrete X} : X -> X -> bool :=
  fun x x' =>
    match eq_dec x x' with
    | left _ => true
    | right _ => false
    end.

Record Material : Type := {
  queen_ct : nat;
  rook_ct : nat;
  bishop_ct : nat;
  knight_ct : nat;
  }.

Definition Material_le (m1 m2 : Material) : Prop :=
  queen_ct m1 <= queen_ct m2 /\
  rook_ct m1 <= rook_ct m2 /\
  bishop_ct m1 <= bishop_ct m2 /\
  knight_ct m1 <= knight_ct m2.

Definition Material_le_dec (m1 m2 : Material) :
  { Material_le m1 m2 } + { ~ Material_le m1 m2 }.
Proof.
  unfold Material_le.
  destruct (Compare_dec.le_dec (queen_ct m1) (queen_ct m2)); [|right; tauto].
  destruct (Compare_dec.le_dec (rook_ct m1) (rook_ct m2)); [|right; tauto].
  destruct (Compare_dec.le_dec (bishop_ct m1) (bishop_ct m2)); [|right; tauto].
  destruct (Compare_dec.le_dec (knight_ct m1) (knight_ct m2)); [|right; tauto].
  left; tauto.
Defined.

Record TotalMaterial : Type := {
  white_material : Material;
  black_material : Material;
  }.

Definition TotalMaterial_le (t1 t2 : TotalMaterial) : Prop :=
  Material_le (white_material t1) (white_material t2) /\
  Material_le (black_material t1) (black_material t2).

Definition TotalMaterial_le_dec (t1 t2 : TotalMaterial) :
  { TotalMaterial_le t1 t2 } + { ~ TotalMaterial_le t1 t2 }.
Proof.
  unfold TotalMaterial_le.
  destruct (Material_le_dec (white_material t1) (white_material t2)); [|right; tauto].
  destruct (Material_le_dec (black_material t1) (black_material t2)); [|right; tauto].
  left; tauto.
Defined.

Lemma Material_le_trans (m1 m2 m3 : Material) :
  Material_le m1 m2 ->
  Material_le m2 m3 ->
  Material_le m1 m3.
Proof.
  intros p1 p2.
  unfold Material_le in *.
  repeat split.
  - apply Nat.le_trans with (m := queen_ct m2); tauto.
  - apply Nat.le_trans with (m := rook_ct m2); tauto.
  - apply Nat.le_trans with (m := bishop_ct m2); tauto.
  - apply Nat.le_trans with (m := knight_ct m2); tauto.
Qed.

Lemma TotalMaterial_le_trans (t1 t2 t3 : TotalMaterial) :
  TotalMaterial_le t1 t2 ->
  TotalMaterial_le t2 t3 ->
  TotalMaterial_le t1 t3.
Proof.
  intros [w1 b1] [w2 b2].
  split.
  - apply Material_le_trans with (m2 := white_material t2); auto.
  - apply Material_le_trans with (m2 := black_material t2); auto.
Qed.

Definition add_queen : Material -> Material :=
  fun m => {|
    queen_ct := S (queen_ct m);
    rook_ct := rook_ct m;
    bishop_ct := bishop_ct m;
    knight_ct := knight_ct m;
  |}.

Definition add_rook : Material -> Material :=
  fun m => {|
    queen_ct := queen_ct m;
    rook_ct := S (rook_ct m);
    bishop_ct := bishop_ct m;
    knight_ct := knight_ct m;
  |}.

Definition add_bishop : Material -> Material :=
  fun m => {|
    queen_ct := queen_ct m;
    rook_ct := rook_ct m;
    bishop_ct := S (bishop_ct m);
    knight_ct := knight_ct m;
  |}.

Definition add_knight : Material -> Material :=
  fun m => {|
    queen_ct := queen_ct m;
    rook_ct := rook_ct m;
    bishop_ct := bishop_ct m;
    knight_ct := S (knight_ct m);
  |}.

Definition empty_mat : Material := {|
  queen_ct := 0;
  rook_ct := 0;
  bishop_ct := 0;
  knight_ct := 0
  |}.

Definition add_piece : Piece -> Material -> Material :=
  fun p =>
    match p with
    | King => id
    | Queen => add_queen
    | Rook => add_rook
    | Bishop => add_bishop
    | Knight => add_knight
    end.

Fixpoint get_material_aux (ps : list (Player * Piece))
  (w : Material) (b : Material) : TotalMaterial :=
  match ps with
  | [] => {| white_material := w; black_material := b; |}
  | (White, p) :: tl => get_material_aux tl (add_piece p w) b
  | (Black, p) :: tl => get_material_aux tl w (add_piece p b)
  end.

Definition get_material (s : ChessState) : TotalMaterial :=
  get_material_aux (all_pieces s) empty_mat empty_mat.

Definition KRvK_mat : Material := {|
  queen_ct := 0;
  rook_ct := 1;
  bishop_ct := 0;
  knight_ct := 0;
  |}.

Definition KRvK_total_mat : TotalMaterial := {|
  white_material := KRvK_mat;
  black_material := empty_mat;
  |}.

Definition KRvK : Game.GameState ChessGame -> Prop :=
  fun s => TotalMaterial_le (get_material s) KRvK_total_mat.

Definition list_count {X} `{Discrete X} (x : X) (l : list X) : nat :=
  List.length (filter (eqb x) l).

Lemma list_count_cons {X} `{Discrete X} (x x' : X) (l : list X) :
  list_count x (x' :: l) =
  if eqb x x' then S (list_count x l) else list_count x l.
Proof.
  unfold list_count.
  simpl.
  destruct eqb; reflexivity.
Qed.

Lemma eqb_Some_Some {X} `{Discrete X} x x' :
  eqb (Some x) (Some x') = eqb x x'.
Proof.
  unfold eqb.
  destruct (eq_dec x x'), (eq_dec (Some x) (Some x')).
  - reflexivity.
  - congruence.
  - congruence.
  - reflexivity.
Qed.

Lemma eqb_Some_None {X} `{Discrete X} x :
  eqb (Some x) None = false.
Proof.
  unfold eqb.
  destruct (eq_dec (Some x) None).
  - congruence.
  - reflexivity.
Qed.

Lemma list_count_filter_Some {X} `{Discrete X} (x : X) (l : list (option X)) :
  list_count x (filter_Some l) = list_count (Some x) l.
Proof.
  induction l as [|[x'|] l'].
  - reflexivity.
  - simpl.
    repeat rewrite list_count_cons.
    rewrite eqb_Some_Some.
    destruct (eqb x x').
    + rewrite IHl'.
      reflexivity.
    + exact IHl'.
  - simpl.
    rewrite list_count_cons.
    rewrite eqb_Some_None.
    exact IHl'.
Qed.

Definition board_count (s : ChessState) (p : Player * Piece) : nat := list_count p (all_pieces s).

Print Mat.

Lemma Mat_to_list_S {m n} {X} (mat : Mat X (S m) n) :
  Mat.to_list mat =
  Vec.to_list (fst mat) ++ Mat.to_list (snd mat).
Proof.
  reflexivity.
Qed.

Lemma list_count_app {X} `{Discrete X} (x : X) (l1 l2 : list X) :
  list_count x (l1 ++ l2) =
  list_count x l1 + list_count x l2.
Proof.
  unfold list_count.
  rewrite filter_app.
  rewrite app_length.
  reflexivity.
Qed.

Lemma list_count_Vec_to_list {n} {X} `{Discrete X} (x : X)
  (v : Vec X n) :
  list_count x (Vec.to_list v) =
  list_sum (map (fun i =>
    match eq_dec x (vaccess i v) with
    | left _ => 1
    | right _ => 0
    end) (Fin.all_fin n)).
Proof.
  induction n.
  - reflexivity.
  - simpl.
    rewrite list_count_cons.
    unfold eqb.
    rewrite IHn.
    rewrite map_map.
    destruct (eq_dec x (fst v)); reflexivity.
Qed.

Lemma list_count_Mat_to_list {m n} {X} `{Discrete X} (x : X)
  (mat : Mat X m n) :
  list_count x (Mat.to_list mat) =
  list_sum (map (fun i => list_count x (Vec.to_list (vaccess i mat))) (Fin.all_fin m)).
Proof.
  induction m.
  - simpl.
    destruct mat.
    reflexivity.
  - rewrite Mat_to_list_S.
    rewrite list_count_app.
    rewrite IHm.
    simpl Fin.all_fin.
    rewrite map_cons.
    rewrite map_map.
    reflexivity.
Qed.

Lemma list_sum_map_all_fin {n} (f g : Fin.Fin n -> nat) :
  (forall i, f i = g i) ->
  list_sum (map f (Fin.all_fin n)) =
  list_sum (map g (Fin.all_fin n)).
Proof.
  induction n.
  - intro; reflexivity.
  - intro Hfg; simpl.
    rewrite Hfg.
    do 2 rewrite map_map.
    f_equal.
    apply IHn.
    intro; apply Hfg.
Qed.

Lemma list_sum_map_all_fin_S {n} (f g : Fin.Fin n -> nat) (i : Fin.Fin n) :
  f i = S (g i) ->
  (forall j, j <> i -> f j = g j) ->
  list_sum (map f (Fin.all_fin n)) =
  S (list_sum (map g (Fin.all_fin n))).
Proof.
  induction n.
  - destruct i.
  - intros Hfgi Hfgni; simpl.
    destruct i as [[]|i].
    + rewrite Hfgi; simpl.
      do 2 f_equal.
      do 2 rewrite map_map.
      apply list_sum_map_all_fin.
      intro j.
      apply Hfgni.
      discriminate.
    + do 2 rewrite map_map.
      rewrite IHn with (i := i) (g := fun j => g (inr j)); auto.
      * rewrite Hfgni; [|discriminate].
        apply Nat.add_succ_r.
      * intros j Hj.
        apply Hfgni.
        congruence.
Qed.

Lemma list_sum_nz (xs : list nat) (n : nat) :
  n <> 0 -> In n xs -> list_sum xs <> 0.
Proof.
  induction xs; intros n_nz n_in.
  - destruct n_in.
  - simpl.
    destruct n_in as [|n_in].
    + lia.
    + specialize (IHxs n_nz n_in).
      lia.
Qed.

Lemma list_sum_map_all_fin_P {n} (f g : Fin.Fin n -> nat) (i : Fin.Fin n) :
  g i = S (f i) ->
  (forall j, j <> i -> f j = g j) ->
  list_sum (map f (Fin.all_fin n)) =
  pred (list_sum (map g (Fin.all_fin n))).
Proof.
  induction n.
  - destruct i.
  - intros Hfgi Hfgni; simpl.
    destruct i as [[]|i].
    + rewrite Hfgi; simpl.
      f_equal.
      do 2 rewrite map_map.
      apply list_sum_map_all_fin.
      intro j.
      apply Hfgni; discriminate.
    + do 2 rewrite map_map.
      rewrite IHn with (i := i) (g := fun j => g (inr j)); auto.
      * rewrite Hfgni; [|discriminate].
        apply Nat.add_pred_r.
        apply list_sum_nz with (n := g (inr i)).
        -- congruence.
        -- apply in_map with (f := fun j => g (inr j)).
           apply Fin.all_fin_In.
      * intros.
        apply Hfgni; congruence.
Qed.

Lemma vupdate_vaccess {n} {X} (v : Vec X n) (i : Fin.Fin n) :
  vupdate i (vaccess i v) v = v.
Proof.
  induction n.
  - destruct i.
  - destruct i; simpl.
    + destruct v; reflexivity.
    + rewrite IHn.
      destruct v; reflexivity.
Qed.

Lemma list_count_mupdate {m n} {X} `{Discrete X} (x x' : X)
  (mat : Mat X m n) (i : Fin.Fin m) (j : Fin.Fin n) :
  list_count x (Mat.to_list (mupdate i j x' mat)) =
  match eq_dec x x' with
  | left _ =>
    match eq_dec x (maccess i j mat) with
    | left _ => list_count x (Mat.to_list mat)
    | right _ => S (list_count x (Mat.to_list mat))
    end
  | right _ =>
    match eq_dec x (maccess i j mat) with
    | left _ => pred (list_count x (Mat.to_list mat))
    | right _ => list_count x (Mat.to_list mat)
    end
  end.
Proof.
  destruct (eq_dec x x') as [xx'_eq|xx'_neq].
  - subst.
    destruct (eq_dec x' (maccess i j mat)) as [Hx'|Hx'].
    + do 2 rewrite list_count_Mat_to_list.
      apply list_sum_map_all_fin.
      intro k.
      destruct (eq_dec k i) as [Hik|Hik].
      * subst.
        unfold mupdate.
        rewrite vaccess_vupdate_eq.
        unfold maccess at 2.
        rewrite vupdate_vaccess.
        reflexivity.
      * unfold mupdate.
        rewrite vaccess_vupdate_neq; auto.
    + do 2 rewrite list_count_Mat_to_list.
      apply list_sum_map_all_fin_S with (i := i).
      * unfold mupdate.
        rewrite vaccess_vupdate_eq.
        do 2 rewrite list_count_Vec_to_list.
        apply list_sum_map_all_fin_S with (i := j).
        -- rewrite vaccess_vupdate_eq.
           destruct eq_dec; [|contradiction].
           destruct eq_dec; [contradiction|].
           reflexivity.
        -- intros k Hk.
           rewrite vaccess_vupdate_neq; auto.
      * intros k Hk.
        unfold mupdate.
        rewrite vaccess_vupdate_neq; auto.
  - destruct (eq_dec x (maccess i j mat)) as [Hx|Hx].
    + subst.
      do 2 rewrite list_count_Mat_to_list.
      apply list_sum_map_all_fin_P with (i := i).
      * do 2 rewrite list_count_Vec_to_list.
        apply list_sum_map_all_fin_S with (i := j).
        -- unfold maccess, mupdate.
           do 2 rewrite vaccess_vupdate_eq.
           destruct eq_dec; [|contradiction].
           destruct eq_dec; [contradiction|].
           reflexivity.
        -- intros k Hk.
           unfold mupdate.
           rewrite vaccess_vupdate_eq.
           rewrite vaccess_vupdate_neq; auto.
      * intros k Hk.
        unfold mupdate.
        rewrite vaccess_vupdate_neq; auto.
    + do 2 rewrite list_count_Mat_to_list.
      apply list_sum_map_all_fin.
      intro k.
      do 2 rewrite list_count_Vec_to_list.
      apply list_sum_map_all_fin.
      intro l.
      unfold mupdate.
      destruct (eq_dec k i) as [Hk|Hk].
      * subst.
        rewrite vaccess_vupdate_eq.
        destruct (eq_dec l j) as [Hl|Hl].
        -- subst.
           rewrite vaccess_vupdate_eq.
           destruct eq_dec; [contradiction|].
           destruct eq_dec; [contradiction|].
           reflexivity.
        -- rewrite vaccess_vupdate_neq; auto.
      * rewrite vaccess_vupdate_neq; auto.
Qed.

Lemma count_exec_Move_le (s : ChessState) (m : ChessMove s) (c : Player.Player) (p : Piece) :
  board_count (exec_ChessMove m) (c, p) <=
  board_count s (c, p).
Proof.
  unfold board_count.
  destruct m; simpl.
  pose proof (dest_orig_neq r) as do_neq.
  destruct r; simpl in *.
  unfold all_pieces.
  unfold exec_RegularMove.
  simpl board.
  unfold updated_board.
  unfold clear.
  unfold place_piece.
  destruct premove; simpl in do_neq.
  unfold Chess.origin.
  destruct origin as [[i] [j]].
  unfold Chess.dest.
  destruct dest as [[i'] [j']].
  unfold Chess.piece.
  repeat rewrite list_count_filter_Some.
  rewrite list_count_mupdate.
  destruct eq_dec; [congruence|].
  destruct eq_dec as [pf1|pf1].
  - rewrite list_count_mupdate.
    destruct eq_dec; destruct eq_dec; lia.
  - rewrite list_count_mupdate.
    destruct eq_dec as [pf2|pf2].
    + destruct eq_dec as [pf3|pf3].
      * lia.
      * rewrite maccess_mupdate_neq in pf1.
        -- pose proof (origin_lookup premove_legal) as pf.
           simpl in pf.
           elim pf1.
           rewrite pf2.
           symmetry; exact pf.
        -- intro H.
           apply do_neq.
           inversion H; reflexivity.
    + destruct eq_dec as [pf3|pf3].
      * lia.
      * lia.
Qed.

Lemma get_material_aux_correct (l : list (Player * Piece)) : forall (mw mb : Material),
  get_material_aux l mw mb = {|
    white_material := {|
      queen_ct := list_count (White, Queen) l + queen_ct mw;
      rook_ct := list_count (White, Rook) l + rook_ct mw;
      bishop_ct := list_count (White, Bishop) l + bishop_ct mw;
      knight_ct := list_count (White, Knight) l + knight_ct mw;
    |};
    black_material := {|
      queen_ct := list_count (Black, Queen) l + queen_ct mb;
      rook_ct := list_count (Black, Rook) l + rook_ct mb;
      bishop_ct := list_count (Black, Bishop) l + bishop_ct mb;
      knight_ct := list_count (Black, Knight) l + knight_ct mb;
    |};
  |}.
Proof.
  induction l as [|[c p] l']; intros mw mb.
  - simpl.
    destruct mw,mb; reflexivity.
  - destruct c, p; simpl.
    + repeat rewrite list_count_cons; simpl.
      unfold id.
      rewrite IHl'.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      unfold id.
      rewrite IHl'.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
    + repeat rewrite list_count_cons; simpl.
      rewrite IHl'; simpl.
      rewrite Nat.add_succ_r.
      reflexivity.
Qed.

Lemma get_material_correct (s : ChessState) :
  get_material s = {|
    white_material := {|
      queen_ct := board_count s (White, Queen);
      rook_ct := board_count s (White, Rook);
      bishop_ct := board_count s (White, Bishop);
      knight_ct := board_count s (White, Knight);
    |};
    black_material := {|
      queen_ct := board_count s (Black, Queen);
      rook_ct := board_count s (Black, Rook);
      bishop_ct := board_count s (Black, Bishop);
      knight_ct := board_count s (Black, Knight);
    |};
  |}.
Proof.
  unfold get_material.
  rewrite get_material_aux_correct.
  unfold empty_mat; simpl.
  repeat rewrite Nat.add_0_r.
  unfold board_count.
  reflexivity.
Qed.

Lemma Material_le_exec_move_white (s : Game.GameState ChessGame) (m : ChessMove s) :
  Material_le (white_material (get_material (exec_ChessMove m)))
  (white_material (get_material s)).
Proof.
  repeat rewrite get_material_correct; simpl.
  repeat split; apply count_exec_Move_le.
Qed.

Lemma Material_le_exec_move_black (s : Game.GameState ChessGame) (m : ChessMove s) :
  Material_le (black_material (get_material (exec_ChessMove m)))
  (black_material (get_material s)).
Proof.
  repeat rewrite get_material_correct; simpl.
  repeat split; apply count_exec_Move_le.
Qed.

Lemma TotalMaterial_le_exec_move (s : Game.GameState ChessGame) (m : ChessMove s) :
  TotalMaterial_le (get_material (Game.exec_move s m)) (get_material s).
Proof.
  split.
  - apply Material_le_exec_move_white.
  - apply Material_le_exec_move_black.
Qed.
