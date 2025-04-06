Require Import Lia.

Require Import Chess.Chess.Chess.
Require Import Games.Game.Player.
Require Import Games.Game.Win.
Require Import Games.Game.Forces.
Require Import Games.Util.Dec.

Require Import Chess.Util.Fin.

Definition only_king (p : Player) (s : ChessState) : Prop :=
  forall pos piece,
    lookup_piece pos (board s) = Some (p, piece) ->
    piece = King.

Lemma only_king_cannot_checkmate p s :
  only_king p s ->
  ~ atomic_chess_res s = Some (Game.Win p).
Proof.
  intros Hs pf.
  unfold atomic_chess_res in pf.
  destruct enum_chess_moves; [|discriminate].
  - destruct dec; [|discriminate].
    
 admit.

Admitted.

(** QKvK position with white to play or black to play with white queen not
    being threatened by the black king; and the position is not stalemate.
*)
Record t (s : ChessState) : Type := {
  white_queen : Pos;
  lookup_white_queen : lookup_piece white_queen (board s) =
    Some (White, Queen);
  white_pieces : forall pos piece,
    lookup_piece pos (board s) = Some (White, piece) ->
    pos = white_queen \/ pos = white_king s;
  black_pieces : forall pos piece,
    lookup_piece pos (board s) = Some (Black, piece) ->
    pos = black_king s;
  white_queen_unthreatened :
    chess_to_play s = Black ->
    neighbor_adj (board s) (black_king s) white_queen ->
    neighbor_adj (board s) (white_king s) white_queen;
  not_stalemate :
    atomic_chess_res s <> Some Game.Draw;
  }.

Arguments white_queen {_}.
Arguments lookup_white_queen {_}.
Arguments white_pieces {_}.
Arguments black_pieces {_}.
Arguments white_queen_unthreatened {_}.
Arguments not_stalemate {_}.

Lemma black_only_king s : t s -> only_king Black s.
Proof.
  intros t pos piece pf.
  assert (pos = black_king s) by (apply t in pf; auto); subst.
  rewrite lookup_black_king in pf.
  inversion pf; auto.
Qed.

Module cutoff.

(** QKvK position with WQ cutting off BK into a quadrant while not being
    stalemated. This means that both the rank and file for WQ and BK are
    distinct and furthermore, the WK is not interfering the WQ.
**)
Record t (s : ChessState) : Type := {
  mat : QKvK.t s;
  rank_distinct : rank (white_queen mat) <> rank (black_king s);
  file_distinct : file (white_queen mat) <> file (black_king s);
  no_rank_interference :
    rank (white_queen mat) = rank (white_king s) ->
    file_sbetween
      (file (white_king s))
      (file (white_queen mat))
      (file (black_king s));
  no_file_interference :
    file (white_queen mat) = file (white_king s) ->
    rank_sbetween
      (rank (white_king s))
      (rank (white_queen mat))
      (rank (black_king s));
  }.

Arguments mat {_}.
Arguments rank_distinct {_}.
Arguments file_distinct {_}.
Arguments no_rank_interference {_}.
Arguments no_file_interference {_}.

Definition sum1 {X} (F G : X -> Type) : X -> Type :=
  fun X => (F X + G X)%type.

Lemma pforced : @pforces ChessGame White QKvK.t (sum1 t (@awin ChessGame White)).
Proof.
  intros s mat.
  destruct (atomic_chess_res s) eqn:s_res.
  - destruct r.
    + destruct p.
      * apply atom_force; right.
        exact s_res.
      * apply only_king_cannot_checkmate in s_res; [tauto|].
        apply black_only_king; auto.
    + elim (not_stalemate mat); auto.
  - destruct (chess_to_play s) eqn:s_play.
    + destruct (eq_dec (rank (white_queen mat)) (rank (black_king s))).
      * destruct (eq_dec (rank (white_queen mat)) (rank (white_king s))).
        -- admit.
        -- eelim (opp_to_play_not_in_check s); rewrite s_play.
           ++ apply lookup_black_king.
           ++ exists (white_queen mat), Queen; split; [apply mat|].
              right; left.
              split; [exact e|].
              intros p Hp1 Hp2.
              destruct (lookup_piece p (board s)) eqn:Hp3; auto.
              destruct p0 as [[|] pc].
              ** apply (white_pieces mat) in Hp3.
                 destruct Hp3; subst.
                 --- admit. (* contra Hp2 *)
                 --- elim n.
                     apply Hp1.
              ** apply (black_pieces mat) in Hp3; subst.
                 admit. (* contra Hp2 *)
      * destruct (eq_dec (file (white_queen mat)) (file (black_king s))).
        -- admit.
        -- apply atom_force; left.
           unshelve econstructor; auto.
           ++ admit.
           ++ admit.
    + admit.
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








