
Record Group : Type := {
  carrier :> Type;

  id : carrier;
  mult : carrier -> carrier -> carrier;
  inv : carrier -> carrier;

  id_left : forall x, mult id x = x;
  id_right : forall x, mult x id = x;

  mult_assoc : forall x y z, mult (mult x y) z = mult x (mult y z);

  inv_left : forall x, mult (inv x) x = id;
  inv_right : forall x, mult x (inv x) = id;
  }.

Arguments id {_}.
Arguments mult {_} _ _.

Infix "#" := mult (at level 100).
