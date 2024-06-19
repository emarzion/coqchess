Require Import Lia.

Require Import Chess.Chess.
Require Import Games.Game.Player.
Require Import Games.Game.Win.
Require Import Games.Game.Forces.
Require Import Games.Util.Dec.

Require Import Chess.Util.Fin.

(** QKvK position with white to play *)
Record t (s : ChessState) : Type := {
  white_to_play : chess_to_play s = White;
  white_queen : Pos;
  lookup_white_queen : lookup_piece white_queen (board s) =
    Some (White, Queen);
  white_pieces : forall pos piece,
    lookup_piece pos (board s) = Some (White, piece) ->
    pos = white_queen \/ pos = white_king s;
  black_pieces : forall pos piece,
    lookup_piece pos (board s) = Some (Black, piece) ->
    pos = black_king s
  }.

Arguments white_to_play {_}.
Arguments white_queen {_}.
Arguments lookup_white_queen {_}.
Arguments white_pieces {_}.
Arguments black_pieces {_}.

Definition rank_val (r : Rank) : nat :=
  match r with
  | MkRank i => val i
  end.

Definition rank_ascend (p1 p2 : Pos) : Prop :=
  rank_val (rank p1) < rank_val (rank p2).

Module cutoff.
(** QKvK position with white queen and black king
    on distinct ranks *)
Record t (s : ChessState) : Type := {
  material : QKvK.t s;
  rank_distinct : rank (white_queen material) <> rank (black_king s)
  }.

Arguments material {_}.
Arguments rank_distinct {_}.

Lemma pforced : @pforces ChessGame White QKvK.t t.
Proof.
  intros s mat.
  destruct (eq_dec (rank (white_queen mat)) (rank (white_king s))).
Admitted.

End cutoff.

(* Lemma rank_ascending_forces :
  pforces White QKvK_white rank_ascending_QKvK_white.
Proof.
Admitted.

Theorem QKvK_white_win : forall s, QKvK_white s -> win White s.
Proof.
  intros s r.
  apply forces_win.
  eapply pforces_trans; eauto.
  - exact rank_ascending_forces.
  - admit.
Admitted.
 *)








