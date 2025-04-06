Require Import List.
Import ListNotations.

Require Import Chess.Chess.Chess.
Require Import Games.Game.Player.

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
