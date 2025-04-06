Require Import List.
Import ListNotations.

Fixpoint filter_Some {X} (l : list (option X)) : list X :=
  match l with
  | [] => []
  | o :: l' =>
    match o with
    | Some x => x :: filter_Some l'
    | None => filter_Some l'
    end
  end.
