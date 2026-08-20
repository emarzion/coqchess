Require Import List.
Require Import Lia.
Import ListNotations.
Require Import String.

Require Import TBGen.StratSymTB.OCamlTB.

Require Import Games.Util.Dec.
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

Record EditBoard : Type := {
  edit_to_play : Player;
  edit_board : Board;
  }.

Definition init_edit : EditBoard := {|
  edit_to_play := White;
  edit_board := blank_board;
  |}.

Definition mkPreChessState (e : EditBoard) :
  Error PreChessState.
Proof.
  pose (b := edit_board e).
  pose (pl := edit_to_play e).
  pose (m := mp_of_board (edit_board e)).
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
    match pl with
    | White => bk
    | Black => wk
    end).
  refine (mbind (guard
    (negb (is_threatened_byb b opp_king pl))
    illegal_check_msg)
    (fun _ => _)).
  exact (mret {|
    pre_chess_to_play := pl;
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

Lemma mkPreChessState_white_king e :
  lift (fun s => lookup_piece (pre_white_king s) (pre_board s)
  = Some (White, King)) (mkPreChessState e).
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

Lemma mkPreChessState_black_king e :
  lift (fun s => lookup_piece (pre_black_king s) (pre_board s)
  = Some (Black, King)) (mkPreChessState e).
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

Lemma mkPreChessState_kings_unique e :
  lift (fun s => forall pl pos,
    lookup_piece pos (pre_board s) = Some (pl, King) ->
    pos = pre_king s pl) (mkPreChessState e).
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

Lemma mkPreChessState_no_check e :
  lift (fun s => forall pos,
    lookup_piece pos (pre_board s) =
    Some (opp (pre_chess_to_play s), King) ->
    ~ is_threatened_by (pre_board s) pos (pre_chess_to_play s))
  (mkPreChessState e).
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
  destruct edit_to_play.
  - simpl in *; rewrite pf_bk in pf_look.
    destruct pf_look as [|[]]; now subst.
  - simpl in *; rewrite pf_wk in pf_look.
    destruct pf_look as [|[]]; now subst.
Qed.

Lemma mkPreChessState_is_bound e :
  lift (fun s => forall pl pc,
    count pl pc (pre_board s) <= KRvK pl pc)
  (mkPreChessState e).
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

Definition mk_KRvK_bound (e : EditBoard) :
  Error ChessState.
Proof.
  pose proof (
    (mkPreChessState_white_king e) */\
    (mkPreChessState_black_king e) */\
    (mkPreChessState_kings_unique e) */\
    (mkPreChessState_no_check e)
  ) as pfs.
  refine (cond_monad_map
    (mkPreChessState e) pfs _).
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

Lemma mk_KRvK_material_bound e :
  lift (material_bound KRvK) (mk_KRvK_bound e).
Proof.
  unfold mk_KRvK_bound.
  eapply lift_cond_monad_map;
    [|apply mkPreChessState_is_bound].
  simpl; intros s Hs [? [? [? ?]]].
  unfold material_bound; simpl.
  apply Hs.
Qed.

Theorem mk_KRvK_sound e s :
  mk_KRvK_bound e = success s ->
  material_bound KRvK s.
Proof.
  intro pf.
  pose proof (mk_KRvK_material_bound e) as pf'.
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

Definition EditBoard_of_PreChessState (s : PreChessState)
  : EditBoard := {|
  edit_to_play := pre_chess_to_play s;
  edit_board := pre_board s;
  |}.

Lemma pre_mk_KRvK_bound_returns : forall s,
  material_bound KRvK s ->
  returns
  (mkPreChessState
    (EditBoard_of_PreChessState
      (PreChessState_of_ChessState s)
    ))
  (PreChessState_of_ChessState s).
Proof.
  intros s Hs.
  unfold PreChessState_of_ChessState.
  unfold EditBoard_of_PreChessState.
  unfold mkPreChessState.
  simpl.
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
  exists e,
    returns (mk_KRvK_bound e) s.
Proof.
  intros s Hs.
  exists {|
    edit_to_play := chess_to_play s;
    edit_board := board s;
  |}.
  eapply cond_monad_map_returns;
    [apply pre_mk_KRvK_bound_returns|]; auto.
  intros [? [? [? ?]]].
  apply state_ext; simpl; auto.
Qed.

Theorem mk_KRvK_complete : forall s,
  material_bound KRvK s ->
  exists e,
    mk_KRvK_bound e = success s.
Proof.
  exact mk_KRvK_bound_returns.
Qed.

Record EditMove := {
  orig : Pos;
  dest : Pos;
  }.

Definition toggle_player (e : EditBoard) : EditBoard := {|
  edit_to_play := opp (edit_to_play e);
  edit_board := edit_board e;
  |}.

Definition execEditMove (m : EditMove)
  (e : EditBoard) : EditBoard := {|
    edit_to_play := edit_to_play e;
    edit_board :=
      match lookup_piece (orig m) (edit_board e) with
      | Some (pl, pc) =>
          place_piece pl pc (dest m)
            (clear (orig m) (edit_board e))
      | None => edit_board e
      end;
  |}.

Definition verify_legal_msg : string :=
  "Error: verify_legal".

Arguments dec P {_}.

Definition verify_origin (s : ChessState) (m : PreMove) :
  Error (lookup_piece (origin m) (board s) = Some (chess_to_play s, piece m)).
Proof.
  match goal with
  | |- Error ?P => destruct (dec P)
  end.
  - exact (mret e).
  - exact (error verify_legal_msg).
Defined.

Definition verify_dest (s : ChessState) (m : PreMove) :
  Error (open (chess_to_play s) (board s) (Chess.dest m)).
Proof.
  match goal with
  | |- Error ?P => destruct (dec P)
  end.
  - exact (mret o).
  - exact (error verify_legal_msg).
Defined.

Definition verify_adj (s : ChessState) (m : PreMove) :
  Error (non_pawn_piece_adj (piece m) (board s)
    (origin m) (Chess.dest m)).
Proof.
  match goal with
  | |- Error ?P => destruct (dec P)
  end.
  - exact (mret n).
  - exact (error verify_legal_msg).
Defined.

Definition verify_no_chk (s : ChessState) (m : PreMove) :
  Error (
    let upd :=
      (clear (origin m)
        (place_piece (chess_to_play s) 
          (piece m) (Chess.dest m) (board s))) in
      forall pos,
        lookup_piece pos upd = Some (chess_to_play s, King) ->
        ~ is_threatened_by upd pos (opp (chess_to_play s))).
Proof.
  cbv zeta.
  match goal with
  | |- Error ?P => destruct (dec P)
  end.
  - exact (mret n).
  - exact (error verify_legal_msg).
Defined.

Definition verify_legal (s : ChessState) (m : PreMove) : Error (legal s m).
Proof.
  refine (mbind (verify_origin s m) (fun pf1 => _)).
  refine (mbind (verify_dest s m) (fun pf2 => _)).
  refine (mbind (verify_adj s m) (fun pf3 => _)).
  refine (mbind (verify_no_chk s m) (fun pf4 => _)).
  exact (mret {|
    origin_lookup := pf1;
    dest_open := pf2;
    origin_dest_adj := pf3;
    no_resulting_check := pf4;
  |}).
Defined.

Lemma verify_origin_returns s m (pf : legal s m) :
  returns (verify_origin s m) (origin_lookup pf).
Proof.
  unfold verify_origin.
  destruct dec.
  - apply mret_returns_eq.
    apply UIP.UIP.
  - elim n.
    apply pf.
Qed.

Lemma verify_dest_returns s m (pf : legal s m) :
  returns (verify_dest s m) (dest_open pf).
Proof.
  unfold verify_dest.
  destruct dec.
  - apply mret_returns_eq.
    apply UIP.UIP.
  - elim n.
    apply pf.
Qed.

Lemma verify_adj_returns s m (pf : legal s m) :
  returns (verify_adj s m) (origin_dest_adj pf).
Proof.
  unfold verify_adj.
  destruct dec.
  - apply mret_returns_eq.
    apply UIP.UIP.
  - elim n.
    apply pf.
Qed.

Lemma verify_no_chk_returns s m (pf : legal s m) :
  returns (verify_no_chk s m) (no_resulting_check pf).
Proof.
  unfold verify_no_chk.
  destruct dec.
  - apply mret_returns_eq.
    apply UIP.UIP.
  - elim n.
    apply (no_resulting_check pf).
Qed.

Lemma verify_legal_returns s m (pf : legal s m) :
  returns (verify_legal s m) pf.
Proof.
  apply mbind_returns with (x := origin_lookup pf);
    [apply verify_origin_returns|].
  eapply mbind_returns with (x := dest_open pf);
    [apply verify_dest_returns|].
  eapply mbind_returns with (x := origin_dest_adj pf);
    [apply verify_adj_returns|].
  eapply mbind_returns with (x := no_resulting_check pf);
    [apply verify_no_chk_returns|].
  destruct pf.
  apply mret_returns.
Qed.

Definition wrong_color : string :=
  "Error: wrong color".

Definition empty_square : string :=
  "Error: empty square".

Definition buildPreMove (m : EditMove) (e : EditBoard) : Error PreMove :=
  let b := edit_board e in
  let pl := edit_to_play e in
  match lookup_piece (orig m) b with
  | Some (pl', pc) =>
     mbind (guard (player_eqb pl pl') wrong_color) (fun _ =>
     mret {|
        piece := pc;
        origin := orig m;
        Chess.dest := dest m;
      |})
  | None => error empty_square
  end.

Definition forgetPreMove (m : PreMove) : EditMove := {|
  orig := origin m;
  dest := Chess.dest m;
  |}.

Definition forgetRegularMove {s} (m : RegularMove s) : EditMove :=
  forgetPreMove (premove m).

Definition forgetMove {s} (m : ChessMove s) : EditMove :=
  match m with
  | reg_move _ m' => forgetRegularMove m'
  end.

Lemma buildPreMove_returns {s} (m : RegularMove s) :
  returns (buildPreMove (forgetRegularMove m)
    (EditBoard_of_PreChessState (PreChessState_of_ChessState s)))
    (premove m).
Proof.
  unfold buildPreMove.
  destruct m; simpl.
  rewrite (origin_lookup premove_legal).
  eapply mbind_returns.
  - apply guard_returns.
    apply player_eqb_refl.
  - destruct premove.
    apply mret_returns.
Qed.

Definition buildRegularMove (m : EditMove) (s : ChessState)
  : Error (RegularMove s) :=
  mbind (buildPreMove m
    (EditBoard_of_PreChessState
      (PreChessState_of_ChessState s))) (fun m =>
    (mbind (verify_legal s m) (fun pf =>
    mret {|
      premove := m;
      premove_legal := pf
    |}))).

Definition buildMove (m : EditMove) (s : ChessState)
  : Error (ChessMove s) :=
  mbind (buildRegularMove m s) (fun r => mret (reg_move s r)).

Lemma buildRegularMove_returns {s} (r : RegularMove s) :
  returns (buildRegularMove (forgetRegularMove r) s) r.
Proof.
  eapply mbind_returns.
  - apply buildPreMove_returns.
  - apply mbind_returns with (x := premove_legal r).
    + apply verify_legal_returns.
    + destruct r; apply mret_returns.
Qed.

Lemma buildMove_return {s} (m : ChessMove s) :
  returns (buildMove (forgetMove m) s) m.
Proof.
  destruct m.
  eapply mbind_returns.
  - apply buildRegularMove_returns.
  - apply mret_returns.
Qed.

Lemma buildMove_complete s (m : ChessMove s) :
  exists em, buildMove em s = success m.
Proof.
  exists (forgetMove m).
  apply buildMove_return.
Qed.
