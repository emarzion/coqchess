Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.
Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.VecRev.
Require Import Chess.Util.MatAction.
Require Import Chess.Util.PosAction.

Require Import Chess.Chess.Chess.

Lemma maccess_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess (x @ c) (x @ M) = maccess c M.
Proof.
  destruct c as [i j].
  destruct x; simpl.
  - reflexivity.
  - rewrite maccess_transpose.
    rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_vreflect.
    rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_hreflect.
    apply maccess_transpose.
  - rewrite maccess_hreflect.
    reflexivity.
  - rewrite maccess_vreflect.
    reflexivity.
  - rewrite maccess_transpose.
    reflexivity.
  - rewrite maccess_hreflect.
    rewrite maccess_transpose.
    rewrite maccess_hreflect.
    reflexivity.
Qed.

Lemma maccess_mat_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess c (x @ M) = maccess (inv _ x @ c) M.
Proof.
  rewrite <- (act_id c) at 1.
  rewrite <- inv_right with (x := x).
  rewrite <- act_assoc.
  apply maccess_act.
Qed.

Lemma maccess_coord_act {X} {n} c (M : Mat X n n) (x : d8_group) :
  maccess (x @ c) M = maccess c (inv _ x @ M).
Proof.
  rewrite <- (act_id M) at 1.
  rewrite <- inv_right with (x := x).
  rewrite <- act_assoc.
  apply maccess_act.
Qed.

Definition state_act (x : d8_group) (s : ChessState) : ChessState.
Proof.
  refine {|
    chess_to_play := chess_to_play s;
    board := x @ board s;
    white_king := x @ white_king s;
    black_king := x @ black_king s;
    lookup_white_king := _;
    lookup_black_king := _;
    kings_unique := _;
    opp_to_play_not_in_check := _;
  |}.
  - unfold lookup_piece.
    rewrite @maccess_act.
    apply s.
  - unfold lookup_piece.
    rewrite @maccess_act.
    apply s.
  - intros pl pos pf.
    unfold lookup_piece in pf.
    rewrite @maccess_mat_act in pf.
    apply s in pf.
    admit.
  - admit.
Admitted.
