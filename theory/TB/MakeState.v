Require Import List.
Import ListNotations.
Require Import String.

Require Import TBGen.StratSymTB.OCamlTB.

Require Import Games.Game.Player.

Require Import Chess.Chess.
Require Import Chess.TB.TB.
Require Import Chess.TB.Material.Material.
Require Import Chess.TB.MaterialPositions.
Require Import Chess.TB.Material.KRvK.
Require Import StateAction.

Definition KRvK_query
  (tb : OCamlTablebase ChessGame)
  (s : ChessState) : option (Player * nat) :=
  query_TB tb s.

Inductive Error (X : Type) : Type :=
  | success : X -> Error X
  | error : string -> Error X.

Arguments success {X} x.
Arguments error {X} msg.

Definition mret {X} : X -> Error X :=
  success.

Definition mbind {X Y} (e : Error X) (f : X -> Error Y) : Error Y :=
  match e with
  | success x => f x
  | error msg => error msg
  end.

Definition kings_msg :=
  "Error: Position must have exactly one king of each color"%string.

Definition KRvK_msg :=
  "Error: Position is not KRvK"%string.

Definition illegal_check_msg :=
  "Error: Illegal check"%string.

Check mp_of_board.

Definition get_king pl (m : material_positions) : Error Pos :=
  match m pl King with
  | [k] => success k
  | _ => error kings_msg
  end.

Definition verify_one_white_rook (m : material_positions) : Error unit :=
  match m White Rook with
  | [] => success tt
  | [r] => success tt
  | _ => error KRvK_msg
  end.

Definition verify_empty pl pc (m : material_positions) : Error unit :=
  match m pl pc with
  | [] => success tt
  | _ => error KRvK_msg
  end.

Definition guard (b : bool) (msg : string) : Error unit :=
  match b with
  | true => success tt
  | false => error msg
  end.

Definition pre_mk_KRvK_bound (to_play : Player)
  (data : list (Player * Piece * Pos)) :
  Error PreChessState.
Proof.
  pose (b := place_pieces data).
  pose (m := mp_of_board b).
  unfold material_positions in m.
  refine (mbind (get_king White m) (fun wk => _)).
  refine (mbind (get_king Black m) (fun bk => _)).
  refine (mbind (verify_one_white_rook m) (fun _ => _)).
  refine (mbind (verify_empty White Queen m) (fun _ => _)).
  refine (mbind (verify_empty Black Queen m) (fun _ => _)).
  refine (mbind (verify_empty Black Rook m) (fun _ => _)).
  refine (mbind (verify_empty White Bishop m) (fun _ => _)).
  refine (mbind (verify_empty Black Bishop m) (fun _ => _)).
  refine (mbind (verify_empty White Knight m) (fun _ => _)).
  refine (mbind (verify_empty Black Knight m) (fun _ => _)).
  pose (opp_king :=
    match to_play with
    | White => bk
    | Black => wk
    end).
  refine (mbind (guard
    (negb (is_threatened_byb b opp_king to_play))
    illegal_check_msg)
    (fun _ => _)).
  exact (mret {|
    pre_chess_to_play := to_play;
    pre_board := b;
    pre_white_king := wk;
    pre_black_king := bk;
  |}).
Defined.

Definition lift {X} (P : X -> Prop) (m : Error X) : Prop :=
  match m with
  | success x => P x
  | error _ => True
  end.

Definition cond_monad_map {X Y} {P : X -> Prop} (m : Error X) :
  lift P m -> (forall x, P x -> Y) -> Error Y :=
  match m with
  | success x => fun p f => mret (f x p)
  | error msg => fun _ _ => error msg
  end.

Lemma lift_bind {X Y} P Q (m : Error X)
  (f : X -> Error Y) :
  lift P m -> (forall x, P x -> lift Q (f x)) ->
  lift Q (mbind m f).
Proof.
  intros.
  unfold lift in *.
  unfold mbind.
  destruct m; auto.
  apply H0; auto.
Qed.

Lemma get_king_correct pl m :
  lift (fun pos => m pl King = [pos]) (get_king pl m).
Proof.
  unfold get_king, lift.
  destruct (m pl King) as [|k [|]] eqn:k_mp; auto.
Qed.

Lemma lift_triv {X} (m : Error X) :
  lift (fun _ => True) m.
Proof.
  destruct m; simpl; auto.
Qed.

Lemma lift_forall {X Y} (P : Y -> X -> Prop) (m : Error X) :
  (forall y, lift (P y) m) ->
  lift (fun x => forall y, P y x) m.
Proof.
  intros.
  destruct m; simpl in *; auto.
Qed.

Lemma lift_mret {X} (P : X -> Prop) (x : X) :
  P x -> lift P (mret x).
Proof.
  intro p; auto.
Qed.

Lemma lift_guard b msg :
  lift (fun _ => b = true) (guard b msg).
Proof.
  destruct b; simpl; auto.
Qed.

Lemma verify_one_white_rook_correct (m : material_positions) :
  lift (fun _ => List.length (m White Rook) <= 1)
  (verify_one_white_rook m).
Proof.
  unfold verify_one_white_rook.
  destruct m as [|? [|? ?]]; simpl; auto.
Qed.

Lemma verify_empty_correct pl pc m :
  lift (fun _ => m pl pc = [])
  (verify_empty pl pc m).
Proof.
  unfold verify_empty.
  destruct m; simpl; auto.
Qed.

Lemma mk_KRvK_bound_white_king to_play data :
  lift (fun s => lookup_piece (pre_white_king s) (pre_board s)
  = Some (White, King)) (pre_mk_KRvK_bound to_play data).
Proof.
  eapply lift_bind; [apply get_king_correct|].
  intros wk Hwk.
  eapply lift_bind; [apply lift_triv|].
  intros bk _.
  do 9 (eapply lift_bind; [apply lift_triv|]; intros _ _).
  apply lift_mret; simpl in *.
  apply mp_of_board_correct2.
  rewrite Hwk; now left.
Qed.

Lemma mk_KRvK_bound_black_king to_play data :
  lift (fun s => lookup_piece (pre_black_king s) (pre_board s)
  = Some (Black, King)) (pre_mk_KRvK_bound to_play data).
Proof.
  eapply lift_bind; [apply lift_triv|].
  intros wk _.
  eapply lift_bind; [apply get_king_correct|].
  intros bk Hbk.
  do 9 (eapply lift_bind; [apply lift_triv|]; intros _ _).
  apply lift_mret; simpl in *.
  apply mp_of_board_correct2.
  rewrite Hbk; now left.
Qed.

Lemma mk_KRvK_bound_kings_unique to_play data :
  lift (fun s => forall pl pos,
    lookup_piece pos (pre_board s) = Some (pl, King) ->
    pos = pre_king s pl) (pre_mk_KRvK_bound to_play data).
Proof.
  eapply lift_bind; [apply get_king_correct|].
  intros wk wk_uniq.
  eapply lift_bind; [apply get_king_correct|].
  intros bk bk_uniq.
  do 9 (eapply lift_bind; [apply lift_triv|]; intros _ _).
  apply lift_mret; simpl in *; intros pl pos Hpos.
  destruct pl; simpl.
  - apply mp_of_board_correct1 in Hpos.
    rewrite wk_uniq in Hpos.
    now destruct Hpos as [[]|[]].
  - apply mp_of_board_correct1 in Hpos.
    rewrite bk_uniq in Hpos.
    now destruct Hpos as [[]|[]].
Qed.

Lemma mk_KRvK_bound_no_check to_play data :
  lift (fun s => forall pos,
    lookup_piece pos (pre_board s) =
    Some (opp (pre_chess_to_play s), King) ->
    ~ is_threatened_by (pre_board s) pos (pre_chess_to_play s))
  (pre_mk_KRvK_bound to_play data).
Proof.
  eapply lift_bind; [apply get_king_correct|].
  intros wk pf_wk.
  eapply lift_bind; [apply get_king_correct|].
  intros bk pf_bk.
  do 8 (eapply lift_bind; [apply lift_triv|]; intros _ _).
  cbv zeta.
  eapply lift_bind; [apply lift_guard|].
  simpl; intros _ no_thr pos pf_look.
  rewrite Bool.negb_true_iff in no_thr.
  rewrite <- is_threatened_byb_false_iff in no_thr.
  simpl in *.
  apply mp_of_board_correct1 in pf_look.
  intro thr; apply no_thr.
  destruct to_play.
  - simpl in *; rewrite pf_bk in pf_look.
    destruct pf_look as [|[]]; now subst.
  - simpl in *; rewrite pf_wk in pf_look.
    destruct pf_look as [|[]]; now subst.
Qed.

Require Import Lia.

Lemma mk_KRvK_bound_is_bound to_play data :
  lift (fun s => forall pl pc,
    count pl pc (pre_board s) <= KRvK pl pc)
  (pre_mk_KRvK_bound to_play data).
Proof.
  eapply lift_bind; [apply get_king_correct|].
  intros wk pf_wk.
  eapply lift_bind; [apply get_king_correct|].
  intros bk pf_bk.
  eapply lift_bind; [apply verify_one_white_rook_correct|].
  simpl in *; intros _ Hwr.
  do 7 (eapply lift_bind; [apply verify_empty_correct|];
    simpl; intros _ ?).
  eapply lift_bind; [apply lift_triv|]; intros _ _.
  apply lift_mret.
  intros pl pc; simpl.
  rewrite <- mp_of_board_count.
  destruct pl, pc; simpl; try
  match goal with
  | [H : mp_of_board _ ?pl ?pc = _
    |- Datatypes.length (mp_of_board _ ?pl ?pc) <= _ ]
    => rewrite H; simpl; lia
  end.
  auto.
Qed.

Lemma lift_cond_monad_map {X Y} {P Q : X -> Prop} {R : Y -> Prop}
  (m : Error X) (p : lift P m) (f : forall x, P x -> Y) :
  (forall x, Q x -> forall p', R (f x p')) ->
  lift Q m ->
  lift R (cond_monad_map m p f).
Proof.
  intros.
  unfold cond_monad_map.
  destruct m; auto.
  apply lift_mret.
  apply H; auto.
Qed.

Lemma lift_and_intro {X} {P Q : X -> Prop} {m : Error X} :
  lift P m -> lift Q m -> lift (fun x => P x /\ Q x) m.
Proof.
  intros p q.
  unfold lift in *.
  destruct m; auto.
Qed.

Notation "p */\ q" := (lift_and_intro p q)
  (right associativity, at level 55).

Definition mk_KRvK_bound (to_play : Player)
  (data : list (Player * Piece * Pos)) :
  Error ChessState.
Proof.
  pose proof (
    (mk_KRvK_bound_white_king to_play data) */\
    (mk_KRvK_bound_black_king to_play data) */\
    (mk_KRvK_bound_kings_unique to_play data) */\
    (mk_KRvK_bound_no_check to_play data)
  ) as pfs.
  refine (cond_monad_map
    (pre_mk_KRvK_bound to_play data) pfs _).
  intros s [wk [bk [uniq no_chk]]].
  exact {|
    chess_to_play := pre_chess_to_play s;
    board := pre_board s;
    white_king := pre_white_king s;
    black_king := pre_black_king s;
    lookup_white_king := wk;
    lookup_black_king := bk;
    kings_unique := uniq;
    opp_to_play_not_in_check := no_chk
  |}.
Defined.

Lemma mk_KRvK_bound_material_bound to_play data :
  lift (material_bound KRvK) (mk_KRvK_bound to_play data).
Proof.
  unfold mk_KRvK_bound.
  eapply lift_cond_monad_map;
    [|apply mk_KRvK_bound_is_bound].
  simpl; intros s Hs [? [? [? ?]]].
  unfold material_bound; simpl.
  apply Hs.
Qed.

Theorem mk_KRvK_sound to_play data s :
  mk_KRvK_bound to_play data = success s ->
  material_bound KRvK s.
Proof.
  intro pf.
  pose proof (mk_KRvK_bound_material_bound to_play data) as pf'.
  rewrite pf in pf'.
  auto.
Qed.

Definition get_data (s : ChessState) :=
  (White, King, white_king s) ::
  (Black, King, black_king s) ::
  map (pair (White, Rook)) (mp_of_board (board s) White Rook).

Definition returns {X} (m : Error X) (x : X) : Prop :=
  m = success x.

Lemma mret_returns {X} (x : X) :
  returns (mret x) x.
Proof.
  reflexivity.
Qed.

Lemma mret_returns_eq {X} (x x' : X) :
  x = x' ->
  returns (mret x) x'.
Proof.
  intro; subst.
  reflexivity.
Qed.

Lemma mbind_returns {X Y} (m : Error X) (f : X -> Error Y) y :
  forall x, returns m x -> returns (f x) y -> returns (mbind m f) y.
Proof.
  intros.
  unfold returns in *.
  subst; auto.
Qed.

Lemma cond_monad_map_returns {X Y}
  (P : X -> Prop) (m : Error X) y
  (f : forall x, P x -> Y) : forall x,
  returns m x ->
  (forall p, f x p = y) ->
  forall p,
  returns (cond_monad_map m p f) y.
Proof.
  unfold returns.
  intros.
  unfold lift in *.
  unfold cond_monad_map.
  destruct m.
  - inversion H; subst.
    rewrite H0; auto.
  - discriminate.
Qed.

Lemma list_count_zero {X} `{Games.Util.Dec.Discrete X} x xs :
  ~ In x xs -> list_count x xs = 0.
Proof.
  induction xs; intro pf.
  - auto.
  - simpl.
    destruct Games.Util.Dec.eq_dec.
    + elim pf; now left.
    + apply IHxs; intro; apply pf; now right.
Qed.

Lemma list_count_len {X} `{Games.Util.Dec.Discrete X} x xs :
  (forall x', In x' xs -> x = x') ->
  list_count x xs = List.length xs.
Proof.
  induction xs; intro pf.
  - auto.
  - simpl.
    destruct Games.Util.Dec.eq_dec.
    + rewrite IHxs; auto.
      intros; apply pf; now right.
    + elim n.
      apply pf; now left.
Qed.

Lemma mk_board_get_data s :
  material_bound KRvK s ->
  place_pieces (get_data s) = board s.
Proof.
  intro.
  apply place_pieces_eq.
  - unfold get_data.
    intros pl pc p pf.
    destruct pf as [wk|[bk|wr]].
    + inversion wk; subst.
      apply s.
    + inversion bk; subst.
      apply s.
    + rewrite in_map_iff in wr.
      destruct wr as [pos [Hpos1 Hpos2]].
      inversion Hpos1; subst.
      apply mp_of_board_correct2; auto.
  - intros.
    unfold get_data.
    simpl map.
    rewrite map_map.
    specialize (H pl pc).
    destruct pl, pc; simpl in *.
    + rewrite list_count_zero.
      * apply king_count.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_len.
      * rewrite map_length.
        symmetry; apply mp_of_board_count.
      * intros [] pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; auto.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * apply king_count.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
    + rewrite list_count_zero.
      * lia.
      * intro pf.
        rewrite in_map_iff in pf.
        destruct pf as [? [? ?]]; discriminate.
  - simpl. repeat constructor.
    + intros [|].
      * apply (f_equal (fun p =>
          lookup_piece p (board s))) in H0.
        rewrite lookup_black_king in H0.
        rewrite lookup_white_king in H0.
        discriminate.
      * rewrite map_map in H0; simpl.
        rewrite map_id in H0.
        apply mp_of_board_correct2 in H0.
        rewrite lookup_white_king in H0.
        discriminate.
    + intro pf.
      rewrite map_map in pf; simpl.
        rewrite map_id in pf.
        apply mp_of_board_correct2 in pf.
        rewrite lookup_black_king in pf.
        discriminate.
    + rewrite map_map; simpl.
      rewrite map_id.
      apply mp_of_board_NoDup.
Qed.

Lemma get_king_returns : forall s pl,
  returns
    (get_king pl (mp_of_board (board s)))
    (king s pl).
Proof.
  intros s pl.
  unfold get_king.
  rewrite mp_of_board_King.
  reflexivity.
Qed.

Lemma verify_one_white_rook_returns : forall b,
  count White Rook b <= 1 ->
  returns (verify_one_white_rook
    (mp_of_board b))
    tt.
Proof.
  intros.
  unfold verify_one_white_rook.
  rewrite <- mp_of_board_count in H.
  destruct mp_of_board as [|? [|? ?]]; try reflexivity.
  simpl in H; lia.
Qed.

Lemma verify_empty_returns : forall b pl pc,
  count pl pc b <= 0 ->
  returns
    (verify_empty pl pc (mp_of_board b))
    tt.
Proof.
  intros.
  unfold verify_empty.
  rewrite <- mp_of_board_count in H.
  destruct mp_of_board; [reflexivity|].
  simpl in H; lia.
Qed.

Lemma guard_returns b msg :
  b = true ->
  returns (guard b msg) tt.
Proof.
  intro; subst.
  reflexivity.
Qed.

Lemma pre_mk_KRvK_bound_returns : forall s,
  material_bound KRvK s ->
  returns
  (pre_mk_KRvK_bound (chess_to_play s) (get_data s))
  (PreChessState_of_ChessState s).
Proof.
  intros s Hs.
  unfold pre_mk_KRvK_bound.
  rewrite mk_board_get_data; auto.
  eapply mbind_returns; [apply get_king_returns|].
  eapply mbind_returns; [apply get_king_returns|].
  eapply mbind_returns;
    [apply verify_one_white_rook_returns; apply Hs|].
  do 7 (eapply mbind_returns;
    [apply verify_empty_returns; apply Hs|]).
  eapply mbind_returns; [apply guard_returns|].
  - rewrite Bool.negb_true_iff.
    rewrite <- is_threatened_byb_false_iff.
    apply opp_to_play_not_in_check.
    destruct chess_to_play; apply s.
  - apply mret_returns_eq; auto.
Qed.

Lemma mk_KRvK_bound_returns : forall s,
  material_bound KRvK s ->
  exists to_play data,
    returns (mk_KRvK_bound to_play data) s.
Proof.
  intros s Hs.
  exists (chess_to_play s), (get_data s).
  eapply cond_monad_map_returns;
    [apply pre_mk_KRvK_bound_returns|]; auto.
  intros [? [? [? ?]]].
  apply state_ext; simpl; auto.
Qed.

Theorem mk_KRvK_complete : forall s,
  material_bound KRvK s ->
  exists to_play data,
    mk_KRvK_bound to_play data = success s.
Proof.
  exact mk_KRvK_bound_returns.
Qed.
