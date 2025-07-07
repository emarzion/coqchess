Require Import Chess.Util.Group.
Require Import Chess.Util.GroupAction.
Require Import Chess.Util.D8.
Require Import Chess.Util.Mat.
Require Import Chess.Util.Vec.
Require Import Chess.Util.VecRev.
Require Import Chess.Util.MatAction.
Require Import Chess.Util.Fin.

Require Import Chess.Chess.Chess.

Definition pos_act {n} (a : d8_group) (p : Coord n n) : Coord n n :=
  match p with
  | (x, y) =>
    match a with
    | i => (x, y)
    | r90 => (y, Fin_rev x)
    | r180 => (Fin_rev x, Fin_rev y)
    | r270 => (Fin_rev y, x)
    | h => (Fin_rev x, y)
    | v => (x, Fin_rev y)
    | d => (y, x)
    | ad => (Fin_rev y, Fin_rev x)
    end
  end.

Lemma pos_act_id {n} : forall p : Coord n n, pos_act i p = p.
Proof.
  intros [x y].
  reflexivity.
Qed.

Lemma pos_act_assoc {n} : forall (a b : d8_group) (x : Coord n n),
  pos_act a (pos_act b x) = pos_act (a # b) x.
Proof.
  intros a b [x y].
  destruct a,b; unfold pos_act; simpl mult; cbv iota;
  repeat rewrite Fin_rev_Fin_rev; reflexivity.
Qed.

Global Instance d8_coord_action {n} : GroupAction d8_group (Coord n n) := {|
  act := pos_act;
  act_id := pos_act_id;
  act_assoc := pos_act_assoc;
  |}.
