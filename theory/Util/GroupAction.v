Require Import Chess.Util.Group.

Record GroupAction (G : Group) (X : Type) : Type := {
  act : G -> X -> X;

  act_id : forall x, act id x = x;
  act_assoc : forall a b x, act a (act b x) = act (a # b) x;
  }.

Arguments act {_} {_} _ _ _.

Infix "@" := act (at level 90).
