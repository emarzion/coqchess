Require Import Bool.
Import BoolNotations.
Require Import Lia.
Require Import List.
Import ListNotations.

Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Util.Dec.

Require Import Chess.Util.Mat.
Require Import Chess.Util.Fin.
Require Import Chess.Util.UIP.

Inductive Piece :=
  | King : Piece
  | Queen : Piece
  | Rook : Piece
  | Bishop : Piece
  | Knight : Piece
  .

#[export]
Instance Piece_Discrete : Discrete Piece.
Proof.
  constructor.
  unfold decision.
  decide equality.
Defined.

#[export]
Instance Piece_Exhaustible : Exhaustible Piece.
Proof.
  constructor.
  intros P Pd.
  destruct (Pd King); [firstorder|].
  destruct (Pd Queen); [firstorder|].
  destruct (Pd Rook); [firstorder|].
  destruct (Pd Bishop); [firstorder|].
  destruct (Pd Knight); [firstorder|].
  right; intros [[] Hp]; tauto.
Defined.

Definition Board : Type :=
  Mat (option (Player * Piece)) 8 8.

Definition blank_board : Board :=
  mreplicate None.

Definition Rank : Type :=
  Fin 8.

Definition rank_1 : Rank :=
  Fin_of_nat 0.

Definition rank_2 : Rank :=
  Fin_of_nat 1.

Definition rank_3 : Rank :=
  Fin_of_nat 2.

Definition rank_4 : Rank :=
  Fin_of_nat 3.

Definition rank_5 : Rank :=
  Fin_of_nat 4.

Definition rank_6 : Rank :=
  Fin_of_nat 5.

Definition rank_7 : Rank :=
  Fin_of_nat 6.

Definition rank_8 : Rank :=
  Fin_of_nat 7.

Global Instance Fin_Discrete {n} :
  Discrete (Fin n).
Proof.
  constructor.
  induction n.
  - intros [].
  - intros i j.
    destruct i as [[]|i];
    destruct j as [[]|j].
    + now left.
    + now right.
    + now right.
    + destruct (IHn i j).
      * left; congruence.
      * right; congruence.
Defined.

Definition File : Type :=
  Fin 8.

Definition file_a : File :=
  Fin_of_nat 0.

Definition file_b : File :=
  Fin_of_nat 1.

Definition file_c : File :=
  Fin_of_nat 2.

Definition file_d : File :=
  Fin_of_nat 3.

Definition file_e : File :=
  Fin_of_nat 4.

Definition file_f : File :=
  Fin_of_nat 5.

Definition file_g : File :=
  Fin_of_nat 6.

Definition file_h : File :=
  Fin_of_nat 7.

Definition Pos : Type :=
  File * Rank.

Definition file : Pos -> File :=
  fst.

Definition rank : Pos -> Rank :=
  snd.

Definition lookup_piece : Pos -> Board -> option (Player * Piece) := maccess.

Definition place_piece : Player -> Piece -> Pos
  -> Board -> Board :=
  fun pl pc c b => mupdate c (Some (pl, pc)) b.

Definition clear : Pos -> Board -> Board :=
  fun c b => mupdate c None b.

Lemma lookup_clear_eq : forall pos b,
  lookup_piece pos (clear pos b) = None.
Proof.
  intros.
  unfold lookup_piece, clear.
  apply maccess_mupdate_eq.
Qed.

Lemma lookup_clear_neq : forall pos1 pos2 b, pos1 <> pos2 ->
  lookup_piece pos1 (clear pos2 b) =
  lookup_piece pos1 b.
Proof.
  intros.
  unfold lookup_piece, clear.
  rewrite maccess_mupdate_neq; auto.
Qed.

Lemma lookup_place_eq : forall player pos b piece,
  lookup_piece pos (place_piece player piece pos b) =
  Some (player, piece).
Proof.
  intros.
  unfold lookup_piece, place_piece.
  apply maccess_mupdate_eq.
Qed.

Lemma lookup_place_neq : forall player pos1 pos2 b piece,
  pos1 <> pos2 ->
  lookup_piece pos1 (place_piece player piece pos2 b) =
  lookup_piece pos1 b.
Proof.
  intros.
  unfold lookup_piece, place_piece.
  rewrite maccess_mupdate_neq; auto.
Qed.

(** Rank/File Operations *)
Section RF_ops.

Definition white_home_rank : Rank :=
  rank_2.

Definition black_home_rank : Rank :=
  rank_6.

Definition home_rank : Player -> Rank :=
  fun p =>
    match p with
    | White => white_home_rank
    | Black => black_home_rank
    end.

Definition white_back_rank : Rank :=
  rank_8.

Definition black_back_rank : Rank :=
  rank_1.

Definition back_rank : Player -> Rank :=
  fun p =>
    match p with
    | White => white_back_rank
    | Black => black_home_rank
    end.

Definition one_up : Rank -> Rank -> Prop :=
  fun i j =>
    val j = S (val i).

Definition one_down : Rank -> Rank -> Prop :=
  fun i j =>
    val i = S (val j).

Definition one_move : Player -> Rank -> Rank -> Prop :=
  fun p =>
    match p with
    | White => one_up
    | Black => one_down
    end.

Definition two_up : Rank -> Rank -> Prop :=
  fun i j =>
    val j = S (S (val i)).

Definition two_down : Rank -> Rank -> Prop :=
  fun i j =>
    val i = S (S (val i)).

Definition two_move : Player -> Rank -> Rank -> Prop :=
  fun p =>
    match p with
    | White => two_up
    | Black => two_down
    end.

Definition rank_dist : Rank -> Rank -> nat :=
  fun i j =>
    fin_dist i j.

Lemma rank_dist_sym : forall r1 r2 : Rank,
  rank_dist r1 r2 = rank_dist r2 r1.
Proof.
  intros i j.
  apply fin_dist_sym.
Qed.

Definition rank_sbetween : Rank -> Rank -> Rank -> Prop :=
  fun r1 r2 r3 =>
    fin_sbetween r1 r2 r3.

Lemma rank_sbetween_sym : forall r1 r2 r3 : Rank,
  rank_sbetween r1 r2 r3 -> rank_sbetween r3 r2 r1.
Proof.
  intros i j k; unfold rank_sbetween;
  apply fin_sbetween_sym.
Qed.

Definition file_dist : File -> File -> nat :=
  fun i j =>
    fin_dist i j.

Lemma file_dist_sym : forall f1 f2 : File,
  file_dist f1 f2 = file_dist f2 f1.
Proof.
  intros i j.
  apply fin_dist_sym.
Qed.

Definition file_sbetween : File -> File -> File -> Prop :=
  fun f1 f2 f3 =>
    fin_sbetween f1 f2 f3.

Lemma file_sbetween_sym : forall f1 f2 f3 : File,
  file_sbetween f1 f2 f3 -> file_sbetween f3 f2 f1.
Proof.
  intros i j k; unfold file_sbetween;
  apply fin_sbetween_sym.
Qed.

End RF_ops.

(** movement of pieces before obstacles *)
Section PreAdjacencies.

Definition diag_preadj : Pos -> Pos -> Prop :=
  fun p1 p2 =>
    rank_dist (rank p1) (rank p2) =
    file_dist (file p1) (file p2).

Definition L_preadj : Pos -> Pos -> Prop :=
  fun p1 p2 =>
       (    file_dist (file p1) (file p2) = 1
         /\ rank_dist (rank p1) (rank p2) = 2
       )
    \/ (    file_dist (file p1) (file p2) = 2
         /\ rank_dist (rank p1) (rank p2) = 1
       ).

Definition horiz_preadj : Pos -> Pos -> Prop :=
  fun p1 p2 => rank p1 = rank p2.

Definition vert_preadj : Pos -> Pos -> Prop :=
  fun p1 p2 => file p1 = file p2.

Definition neighbor_preadj : Pos -> Pos -> Prop :=
  fun p1 p2 =>
    (rank_dist (rank p1) (rank p2) <= 1 /\
    file_dist (file p1) (file p2) <= 1)%nat.

End PreAdjacencies.

(** Movement of pieces accounting for obstacles. *)
Section Adjacencies.

Definition diag_adj : Board -> Pos -> Pos -> Prop :=
  fun b p1 p2 =>
       diag_preadj p1 p2
    /\ forall p3, diag_preadj p1 p3 ->
       file_sbetween (file p1) (file p3) (file p2) ->
       rank_sbetween (rank p1) (rank p3) (rank p2) ->
       lookup_piece p3 b = None.

Definition horiz_adj : Board -> Pos -> Pos -> Prop :=
  fun b p1 p2 =>
       horiz_preadj p1 p2
    /\ forall p3, horiz_preadj p1 p3 ->
       file_sbetween (file p1) (file p3) (file p2) ->
       lookup_piece p3 b = None.

Definition vert_adj : Board -> Pos -> Pos -> Prop :=
  fun b p1 p2 =>
       vert_preadj p1 p2
    /\ forall p3, vert_preadj p1 p3 ->
       rank_sbetween (rank p1) (rank p3) (rank p2) ->
       lookup_piece p3 b = None.

Definition orthog_adj : Board -> Pos -> Pos -> Prop :=
  fun b p1 p2 => horiz_adj b p1 p2 \/ vert_adj b p1 p2.

Definition diag_orthog_adj : Board -> Pos -> Pos -> Prop :=
  fun b p1 p2 => diag_adj b p1 p2 \/ orthog_adj b p1 p2.

Definition L_adj : Board -> Pos -> Pos -> Prop :=
  fun _ => L_preadj.

Definition neighbor_adj : Board -> Pos -> Pos -> Prop :=
  fun _ => neighbor_preadj.

Definition non_pawn_piece_adj : Piece -> Board -> Pos -> Pos -> Prop :=
  fun p =>
    match p with
    | King => neighbor_adj
    | Queen => diag_orthog_adj
    | Rook => orthog_adj
    | Bishop => diag_adj
    | Knight => L_adj
    end.

#[export]
Instance Dec_non_pawn_piece_adj : forall p b pos1 pos2,
  Dec (non_pawn_piece_adj p b pos1 pos2).
Proof.
  intros p b pos1 pos2.
  constructor.
  destruct p; apply dec.
Defined.

End Adjacencies.

Definition open : Player -> Board -> Pos -> Prop :=
  fun player b pos =>
    match lookup_piece pos b with
    | None => True
    | Some (p, _) => p = opp player
    end.

Definition is_threatened_by : Board -> Pos -> Player -> Prop :=
  fun b pos player =>
    exists pos' piece,
         lookup_piece pos' b = Some (player, piece)
      /\ non_pawn_piece_adj piece b pos' pos.

Record ChessState : Type := {
  chess_to_play : Player;
  board : Board;
  white_king : Pos;
  black_king : Pos;

  lookup_white_king : lookup_piece white_king board
    = Some (White, King);
  lookup_black_king : lookup_piece black_king board
    = Some (Black, King);

  king : Player -> Pos :=
    fun pos =>
      match pos with
      | White => white_king
      | Black => black_king
      end;

  kings_unique : forall player pos,
    lookup_piece pos board = Some (player, King) ->
    pos = king player;
  opp_to_play_not_in_check : forall pos,
    lookup_piece pos board = Some (opp chess_to_play, King) ->
    ~ is_threatened_by board pos chess_to_play

  }.

Definition make_move : Player -> Piece -> Pos -> Pos -> Board -> Board :=
  fun player piece pos1 pos2 b =>
    clear pos1 (place_piece player piece pos2 b).

Record PreMove : Type := {
  piece : Piece;
  origin : Pos;
  dest : Pos
  }.

Record legal (st : ChessState) (pm : PreMove) : Prop := {
  origin_lookup : lookup_piece (origin pm) (board st) = Some (chess_to_play st, piece pm);
  dest_open : open (chess_to_play st) (board st) (dest pm);
  origin_dest_adj : non_pawn_piece_adj (piece pm) (board st) (origin pm) (dest pm);

  updated_board := clear (origin pm) (place_piece (chess_to_play st) (piece pm) (dest pm) (board st));

  no_resulting_check : forall pos,
    lookup_piece pos updated_board = Some (chess_to_play st, King) ->
    ~ is_threatened_by updated_board pos (opp (chess_to_play st))
  }.

Arguments origin_lookup {_} {_}.
Arguments dest_open {_} {_}.
Arguments origin_dest_adj {_} {_}.
Arguments no_resulting_check {_} {_}.

Record RegularMove (st : ChessState) : Type := {
  premove : PreMove;
  premove_legal : legal st premove
  }.

Arguments premove {_}.
Arguments premove_legal {_}.

Lemma RegularMove_ext s : forall m m' : RegularMove s,
  premove m = premove m' -> m = m'.
Proof.
  intros [m1 pf1] [m2 pf2] pf; simpl in *.
  subst; f_equal.
  apply UIP.
Qed.

Lemma dest_orig_neq {st} (m : RegularMove st) :
  dest (premove m) <> origin (premove m).
Proof.
  intro Hdo.
  pose (premove m).
  pose proof (origin_lookup (premove_legal m)) as Ho.
  rewrite <- Hdo in Ho.
  pose proof (dest_open (premove_legal m)) as Hd.
  unfold open in Hd.
  rewrite Ho in Hd.
  symmetry in Hd.
  exact (opp_no_fp _ Hd).
Qed.

Lemma no_king_capture {st} (m : RegularMove st) (p : Player) :
  ~ lookup_piece (dest (premove m)) (board st) = Some (p, King).
Proof.
  intro Hdk.
  destruct (player_id_or_opp (chess_to_play st) p)
    as [Hp|Hp].
  - rewrite <- Hp in Hdk.
    pose proof (dest_open (premove_legal m)) as Hd.
    unfold open in Hd.
    rewrite Hdk in Hd.
    symmetry in Hd.
    exact (opp_no_fp _ Hd).
  - rewrite <- Hp in Hdk.
    pose proof (origin_dest_adj (premove_legal m)) as Hod.
    pose proof (opp_to_play_not_in_check st) as
      Hst_no_check.
    apply (Hst_no_check _ Hdk).
    exists (origin (premove m)), (piece (premove m)).
    split.
    + apply origin_lookup; apply premove_legal.
    + exact Hod.
Qed.

Inductive ChessMove (st : ChessState) : Type :=
  | reg_move : RegularMove st -> ChessMove st.

Definition exec_RegularMove {st} (m : RegularMove st) : ChessState. refine (
    {|
      chess_to_play := opp (chess_to_play st);
      board := updated_board st (premove m) (premove_legal m);
      white_king :=
        match chess_to_play st with
        | White =>
          match piece (premove m) with
          | King => dest (premove m)
          | _ => white_king st
          end
        | Black => white_king st
        end;
      black_king :=
        match chess_to_play st with
        | Black =>
          match piece (premove m) with
          | King => dest (premove m)
          | _ => black_king st
          end
        | White => black_king st
        end;
      lookup_white_king := _;
      lookup_black_king := _;
      kings_unique := _;
      opp_to_play_not_in_check := _
    |} ).
Proof.
  (* lookup_white_king *)
  { destruct (chess_to_play st) eqn:to_play.
    - destruct (eq_dec (piece (premove m)) King) as [Hp|Hp].
      + rewrite Hp.
        unfold updated_board.
        rewrite lookup_clear_neq.
        * rewrite lookup_place_eq; congruence.
        * apply dest_orig_neq.
      + unfold updated_board.
        destruct piece eqn:Hpiece; try contradiction.
        all:
          rewrite lookup_clear_neq;
          [ rewrite lookup_place_neq;
            [ apply lookup_white_king
            | intro Hwkd;
              pose proof (dest_open (premove_legal m)) as Hd;
              unfold open in Hd;
              rewrite <- Hwkd in Hd;
              rewrite lookup_white_king in Hd;
              now rewrite to_play in Hd
            ]
          | intro Hwko;
            pose proof (origin_lookup (premove_legal m)) as Ho;
            rewrite <- Hwko in Ho;
            rewrite Hpiece in Ho;
            now rewrite lookup_white_king in Ho
          ].
    - unfold updated_board.
      rewrite lookup_clear_neq.
      + rewrite lookup_place_neq.
        * apply lookup_white_king.
        * intro Hwkd.
          eapply no_king_capture.
          rewrite <- Hwkd.
          apply lookup_white_king.
      + intro Hwko.
        pose proof (origin_lookup (premove_legal m)) as Ho.
        rewrite <- Hwko in Ho.
        rewrite lookup_white_king in Ho.
        congruence.
  }

  (* lookup_black_king *)
  { destruct (chess_to_play st) eqn:to_play.
    - unfold updated_board.
      rewrite lookup_clear_neq.
      + rewrite lookup_place_neq.
        * apply lookup_black_king.
        * intro Hbkd.
          eapply no_king_capture.
          rewrite <- Hbkd.
          apply lookup_black_king.
      + intro Hbko.
        pose proof (origin_lookup (premove_legal m)) as Ho.
        rewrite <- Hbko in Ho.
        rewrite lookup_black_king in Ho.
        congruence.
    - destruct (eq_dec (piece (premove m)) King) as [Hp|Hp].
      + rewrite Hp.
        unfold updated_board.
        rewrite lookup_clear_neq.
        * rewrite lookup_place_eq; congruence.
        * apply dest_orig_neq.
      + unfold updated_board.
        destruct piece eqn:Hpiece; try contradiction.
        all:
          rewrite lookup_clear_neq;
          [ rewrite lookup_place_neq;
            [ apply lookup_black_king
            | intro Hbkd;
              pose proof (dest_open (premove_legal m)) as Hd;
              unfold open in Hd;
              rewrite <- Hbkd in Hd;
              rewrite lookup_black_king in Hd;
              now rewrite to_play in Hd
            ]
          | intro Hbko;
            pose proof (origin_lookup (premove_legal m)) as Ho;
            rewrite <- Hbko in Ho;
            rewrite Hpiece in Ho;
            now rewrite lookup_black_king in Ho
          ].
  }

  (* kings_unique *)
  { intros p pos Hk.
    destruct p.
    - destruct (chess_to_play st) eqn:Hto_play.
      + destruct piece eqn:Hpiece.
        { destruct (eq_dec pos (dest (premove m))); auto.
          unfold updated_board in Hk.
          assert (pos <> origin (premove m)) as Hpo_neq.
          { intro Hpo.
            rewrite Hpo in Hk.
            now rewrite lookup_clear_eq in Hk.
          }
          rewrite lookup_clear_neq in Hk; auto.
          rewrite lookup_place_neq in Hk; auto.
          elim Hpo_neq.
          rewrite (kings_unique st White pos Hk).
          symmetry.
          apply (kings_unique st White).
          rewrite <- Hpiece.
          rewrite <- Hto_play.
          apply origin_lookup.
          apply m.
        }
        all: unfold updated_board in Hk;
          rewrite lookup_clear_neq in Hk;
          [ rewrite lookup_place_neq in Hk;
             [ now apply (kings_unique st White)
             | intro Hpd;
               rewrite Hpd in Hk;
               rewrite lookup_place_eq in Hk;
               congruence
             ]
          | intro Hpo;
            rewrite Hpo in Hk;
            now rewrite lookup_clear_eq in Hk
          ].
      + unfold updated_board in Hk.
        rewrite lookup_clear_neq in Hk.
        * rewrite lookup_place_neq in Hk.
          ** exact (kings_unique st White _ Hk).
          ** intro Hpd.
             rewrite Hpd in Hk.
             rewrite lookup_place_eq in Hk.
             congruence.
        * intro Hpo.
          rewrite Hpo in Hk.
          now rewrite lookup_clear_eq in Hk.
    - destruct (chess_to_play st) eqn:Hto_play.
      + unfold updated_board in Hk.
        rewrite lookup_clear_neq in Hk.
        * rewrite lookup_place_neq in Hk.
          ** exact (kings_unique st Black _ Hk).
          ** intro Hpd.
             rewrite Hpd in Hk.
             rewrite lookup_place_eq in Hk.
             congruence.
        * intro Hpo.
          rewrite Hpo in Hk.
          now rewrite lookup_clear_eq in Hk.
      + destruct piece eqn:Hpiece.
        { destruct (eq_dec pos (dest (premove m))); auto.
          unfold updated_board in Hk.
          assert (pos <> origin (premove m)) as Hpo_neq.
          { intro Hpo.
            rewrite Hpo in Hk.
            now rewrite lookup_clear_eq in Hk.
          }
          rewrite lookup_clear_neq in Hk; auto.
          rewrite lookup_place_neq in Hk; auto.
          elim Hpo_neq.
          rewrite (kings_unique st Black pos Hk).
          symmetry.
          apply (kings_unique st Black).
          rewrite <- Hpiece.
          rewrite <- Hto_play.
          apply origin_lookup.
          apply m.
        }
        all: unfold updated_board in Hk;
          rewrite lookup_clear_neq in Hk;
          [ rewrite lookup_place_neq in Hk;
             [ now apply (kings_unique st Black)
             | intro Hpd;
               rewrite Hpd in Hk;
               rewrite lookup_place_eq in Hk;
               congruence
             ]
          | intro Hpo;
            rewrite Hpo in Hk;
            now rewrite lookup_clear_eq in Hk
          ].
  }

  (* opp_to_play_not_in_check *)
  { intros pos Hpos.
    eapply no_resulting_check.
    rewrite opp_invol in Hpos.
    exact Hpos.
  }
Defined.

Definition exec_ChessMove {st} (m : ChessMove st) : ChessState :=
  match m with
  | reg_move _ r => exec_RegularMove r
  end.

Lemma chess_to_play_exec_ChessMove {st} (m : ChessMove st) :
  chess_to_play (exec_ChessMove m) = opp (chess_to_play st).
Proof.
  destruct m.
  reflexivity.
Defined.

Definition all_piece : list Piece :=
  [King; Queen; Rook; Bishop; Knight].

Lemma all_piece_In : forall p : Piece,
  In p all_piece.
Proof.
  unfold all_piece.
  intros []; simpl; tauto.
Qed.

Definition all_rank : list Rank :=
  all_fin 8.

Lemma all_rank_In : forall r : Rank,
  List.In r all_rank.
Proof.
  intro; apply all_fin_In.
Qed.

Definition all_file : list File :=
  all_fin 8.

Lemma all_file_In : forall f : File,
  List.In f all_file.
Proof.
  intro; apply all_fin_In.
Qed.

Definition all_pos : list Pos :=
  List.concat
    (List.map (fun f : File =>
      List.map (pair f) all_rank) all_file).

Lemma all_pos_In : forall p : Pos,
  List.In p all_pos.
Proof.
  intros [f r].
  unfold all_pos.
  rewrite List.in_concat.
  eexists.
  split.
  - apply List.in_map.
    apply all_file_In.
  - apply List.in_map.
    apply all_rank_In.
Qed.

Fixpoint filter_dec {X} (P : X -> Prop) `{forall x, Dec (P x)}
  (xs : list X) : list {x : X & P x} :=
  match xs with
  | [] => []
  | x :: ys =>
    match dec with
    | left pf => existT P x pf :: filter_dec P ys
    | right _ => filter_dec P ys
    end
  end.

Lemma In_filter_dec {X} (P : X -> Prop) `{forall x, Dec (P x)} :
  forall xs x (pf : P x), In x xs -> In (existT P x pf) (filter_dec P xs).
Proof.
  induction xs; intros.
  - destruct H0.
  - destruct H0.
    + simpl.
      destruct dec.
      * left.
        destruct H0.
        f_equal. apply UIP.
      * congruence.
    + simpl.
      destruct dec; [right|idtac]; apply IHxs; auto.
Qed.

#[export]
Instance Dec_open : forall player b pos, Dec (open player b pos).
Proof.
  intros.
  constructor.
  unfold open.
  destruct (lookup_piece pos b).
  - destruct p.
    apply dec.
  - apply dec.
Defined.

#[export]
Instance Dec_not {P}`{Dec P} : Dec (~ P).
Proof.
  apply impl_Dec.
Defined.

Fixpoint Somes_with_proofs {X Y} (f : X -> option Y)
  (xs : list X) : list { p : X * Y & f (fst p) = Some (snd p) } :=
  match xs with
  | [] => []
  | x :: xs' =>
    match f x as o return (f x = o -> _) with
    | Some y => fun pf => existT _ (x, y) pf :: Somes_with_proofs f xs'
    | None => fun _ => Somes_with_proofs f xs'
    end eq_refl
  end.

Fixpoint filter_Nones {X} (os : list (option X)) : list X :=
  match os with
  | [] => []
  | None :: os' => filter_Nones os'
  | Some x :: os' => x :: filter_Nones os'
  end.

Fixpoint list_player_pieces_aux (b : Board)
  (positions : list Pos) (player : Player)
  : list (Pos * Piece) :=
  match positions with
  | [] => []
  | p :: positions' =>
    match lookup_piece p b with
    | None => list_player_pieces_aux b positions' player
    | Some (pl, piece) =>
      match eq_dec player pl with
      | left _ => (p, piece) :: list_player_pieces_aux b positions' player
      | right _ => list_player_pieces_aux b positions' player
      end
    end
  end.

Lemma list_player_pieces_aux_correct (b : Board)
  (positions : list Pos) (player : Player) : forall pos piece,
  In (pos, piece) (list_player_pieces_aux b positions player) <->
  In pos positions /\ lookup_piece pos b = Some (player, piece).
Proof.
  induction positions; intros.
  - simpl; tauto.
  - with_strategy opaque [eq_dec] simpl; split; intro.
    + destruct (lookup_piece a b) eqn:?.
      * destruct p.
        destruct (eq_dec player p).
        ** destruct H.
           *** split; [left|idtac]; congruence.
           *** rewrite IHpositions in H.
               tauto.
        ** rewrite IHpositions in H.
           tauto.
      * rewrite IHpositions in H.
        tauto.
    + destruct H.
      destruct H.
      ** rewrite <- H in H0.
         rewrite H0.
         destruct eq_dec; [|contradiction].
         left; congruence.
      ** destruct (lookup_piece a b) eqn:?.
         *** destruct p.
             destruct eq_dec.
             **** right.
                  rewrite IHpositions; tauto.
             **** rewrite IHpositions; tauto.
         *** rewrite IHpositions; tauto.
Qed.

Definition list_player_pieces (b : Board) (player : Player)
  : list (Pos * Piece) :=
  list_player_pieces_aux b all_pos player.

Lemma list_player_pieces_correct (b : Board) (player : Player)
  : forall pos piece,
  In (pos, piece) (list_player_pieces b player) <->
  lookup_piece pos b = Some (player, piece).
Proof.
  intros.
  unfold list_player_pieces.
  rewrite list_player_pieces_aux_correct.
  split; [tauto|].
  intro; split; auto.
  apply all_pos_In.
Qed.

Lemma list_player_pieces_correct2 (b : Board) (player : Player)
  : forall p,
  In p (list_player_pieces b player) ->
  lookup_piece (fst p) b = Some (player, snd p).
Proof.
  intros.
  apply list_player_pieces_correct.
  destruct p; auto.
Qed.

Fixpoint add_pfs {X} {P} (xs : list X) (xs_P : forall x, In x xs ->
 P x) {struct xs} : list {x : X & P x}.
Proof.
  destruct xs.
  - exact [].
  - apply cons.
    + exists x.
      apply xs_P.
      left; reflexivity.
    + apply (add_pfs X P xs).
      intros.
      apply xs_P.
      right; auto.
Defined.

#[export] Instance Forall_Dec {X} {P} `{forall x, Dec (P x)}
  (xs : list X) : Dec (Forall P xs).
Proof.
  constructor.
  induction xs.
  - left.
    constructor.
  - destruct IHxs.
    + destruct (dec (P := (P a))).
      * left; constructor; auto.
      * right; intro.
        inversion H0; auto.
    + right; intro.
      inversion H0; auto.
Defined.

Definition pre_move_origins st : list (Pos * Piece) :=
  list_player_pieces (board st) (chess_to_play st).

Lemma pre_move_origins_correct st :
  forall pos p, In (pos, p) (pre_move_origins st) ->
  lookup_piece pos (board st) = Some (chess_to_play st, p).
Proof.
  intros; apply list_player_pieces_correct.
  auto.
Qed.

Definition king_candidate_destinations
  (st : ChessState) (pos : Pos) : list Pos :=
  map (@projT1 _ _) (filter_dec (neighbor_adj (board st) pos) all_pos).

Lemma king_candidate_destinations_correct1 pos st : forall pos',
  In pos' (king_candidate_destinations st pos) ->
  neighbor_adj (board st) pos pos'.
Proof.
  intros pos' Hpos'.
  unfold king_candidate_destinations in Hpos'.
  rewrite in_map_iff in Hpos'.
  destruct Hpos' as [[pos'' pf] [? _]].
  simpl in *; congruence.
Qed.

Lemma king_candidate_destinations_correct2 pos st : forall pos',
  neighbor_adj (board st) pos pos' ->
  In pos' (king_candidate_destinations st pos).
Proof.
  intros pos' pf.
  unfold king_candidate_destinations.
  rewrite in_map_iff.
  exists (existT _ pos' pf); split.
  - reflexivity.
  - apply In_filter_dec.
    apply all_pos_In.
Qed.

Definition queen_candidate_destinations
  (st : ChessState) (pos : Pos) : list Pos :=
  map (@projT1 _ _) (filter_dec (diag_orthog_adj (board st) pos) all_pos).

Lemma queen_candidate_destinations_correct1 pos st : forall pos',
  In pos' (queen_candidate_destinations st pos) ->
  diag_orthog_adj (board st) pos pos'.
Proof.
  intros pos' Hpos'.
  unfold queen_candidate_destinations in Hpos'.
  rewrite in_map_iff in Hpos'.
  destruct Hpos' as [[pos'' pf] [? _]].
  simpl in *; congruence.
Qed.

Lemma queen_candidate_destinations_correct2 pos st : forall pos',
  diag_orthog_adj (board st) pos pos' ->
  In pos' (queen_candidate_destinations st pos).
Proof.
  intros pos' pf.
  unfold queen_candidate_destinations.
  rewrite in_map_iff.
  exists (existT _ pos' pf); split.
  - reflexivity.
  - apply In_filter_dec.
    apply all_pos_In.
Qed.

Definition rook_candidate_destinations
  (st : ChessState) (pos : Pos) : list Pos :=
  map (@projT1 _ _) (filter_dec (orthog_adj (board st) pos) all_pos).

Print orthog_adj.
Print horiz_adj.

Lemma rook_candidate_destinations_correct1 pos st : forall pos',
  In pos' (rook_candidate_destinations st pos) ->
  orthog_adj (board st) pos pos'.
Proof.
  intros pos' Hpos'.
  unfold rook_candidate_destinations in Hpos'.
  rewrite in_map_iff in Hpos'.
  destruct Hpos' as [[pos'' pf] [? _]].
  simpl in *; congruence.
Qed.

Lemma rook_candidate_destinations_correct2 pos st : forall pos',
  orthog_adj (board st) pos pos' ->
  In pos' (rook_candidate_destinations st pos).
Proof.
  intros pos' pf.
  unfold rook_candidate_destinations.
  rewrite in_map_iff.
  exists (existT _ pos' pf); split.
  - reflexivity.
  - apply In_filter_dec.
    apply all_pos_In.
Qed.

Definition bishop_candidate_destinations
  (st : ChessState) (pos : Pos) : list Pos :=
  map (@projT1 _ _) (filter_dec (diag_adj (board st) pos) all_pos).

Lemma bishop_candidate_destinations_correct1 pos st : forall pos',
  In pos' (bishop_candidate_destinations st pos) ->
  diag_adj (board st) pos pos'.
Proof.
  intros pos' Hpos'.
  unfold bishop_candidate_destinations in Hpos'.
  rewrite in_map_iff in Hpos'.
  destruct Hpos' as [[pos'' pf] [? _]].
  simpl in *; congruence.
Qed.

Lemma bishop_candidate_destinations_correct2 pos st : forall pos',
  diag_adj (board st) pos pos' ->
  In pos' (bishop_candidate_destinations st pos).
Proof.
  intros pos' pf.
  unfold bishop_candidate_destinations.
  rewrite in_map_iff.
  exists (existT _ pos' pf); split.
  - reflexivity.
  - apply In_filter_dec.
    apply all_pos_In.
Qed.

Definition knight_candidate_destinations
  (st : ChessState) (pos : Pos) : list Pos :=
  map (@projT1 _ _) (filter_dec (L_adj (board st) pos) all_pos).

Lemma knight_candidate_destinations_correct1 pos st : forall pos',
  In pos' (knight_candidate_destinations st pos) ->
  L_adj (board st) pos pos'.
Proof.
  intros pos' Hpos'.
  unfold knight_candidate_destinations in Hpos'.
  rewrite in_map_iff in Hpos'.
  destruct Hpos' as [[pos'' pf] [? _]].
  simpl in *; congruence.
Qed.

Lemma knight_candidate_destinations_correct2 pos st : forall pos',
  L_adj (board st) pos pos' ->
  In pos' (knight_candidate_destinations st pos).
Proof.
  intros pos' pf.
  unfold knight_candidate_destinations.
  rewrite in_map_iff.
  exists (existT _ pos' pf); split.
  - reflexivity.
  - apply In_filter_dec.
    apply all_pos_In.
Qed.

Definition candidate_destinations (p : Piece) :
  ChessState -> Pos -> list Pos :=
  match p with
  | King => king_candidate_destinations
  | Queen => queen_candidate_destinations
  | Rook => rook_candidate_destinations
  | Bishop => bishop_candidate_destinations
  | Knight => knight_candidate_destinations
  end.

Lemma candidate_destinations_correct1 pos p st : forall pos',
  In pos' (candidate_destinations p st pos) ->
  non_pawn_piece_adj p (board st) pos pos'.
Proof.
  intros.
  destruct p; simpl.
  - now apply king_candidate_destinations_correct1.
  - now apply queen_candidate_destinations_correct1.
  - now apply rook_candidate_destinations_correct1.
  - now apply bishop_candidate_destinations_correct1.
  - now apply knight_candidate_destinations_correct1.
Qed.

Lemma candidate_destinations_correct2 pos p st : forall pos',
  non_pawn_piece_adj p (board st) pos pos' ->
  In pos' (candidate_destinations p st pos).
Proof.
  destruct p; simpl; intros.
  - now apply king_candidate_destinations_correct2.
  - now apply queen_candidate_destinations_correct2.
  - now apply rook_candidate_destinations_correct2.
  - now apply bishop_candidate_destinations_correct2.
  - now apply knight_candidate_destinations_correct2.
Qed.

Definition openb : Player -> Board -> Pos -> bool :=
  fun player b pos =>
    match lookup_piece pos b with
    | None => true
    | Some (p, _) => player_eqb p (opp player)
    end.

Lemma player_eqb_refl : forall pl,
  player_eqb pl pl = true.
Proof.
  intro pl.
  destruct pl; reflexivity.
Qed.

Lemma openb_iff : forall pl b pos,
  openb pl b pos = true <->
  open pl b pos.
Proof.
  intros; split; intro; unfold open, openb in *;
  destruct (lookup_piece pos b) as [[pl' _]|]; auto.
  - apply player_eqb_true; auto.
  - rewrite H.
    apply player_eqb_refl.
Qed.

Definition is_threatened_byb (b : Board) (pos : Pos) (pl : Player) : bool :=
  if dec (P := is_threatened_by b pos pl) then true else false.

Lemma is_threatened_byb_iff b pos pl :
  is_threatened_by b pos pl <->
  is_threatened_byb b pos pl = true.
Proof.
  unfold is_threatened_byb.
  split; intro pf.
  - destruct dec; [auto|contradiction].
  - destruct dec; [auto|discriminate].
Qed.

Lemma is_threatened_byb_false_iff b pos pl :
  ~ is_threatened_by b pos pl <->
  is_threatened_byb b pos pl = false.
Proof.
  split; intro.
  - apply not_true_is_false.
    intro pf.
    apply H.
    rewrite is_threatened_byb_iff; auto.
  - intro pf.
    rewrite is_threatened_byb_iff in pf; congruence.
Qed.

Definition get_PreMoves (st : ChessState) :
  list PreMove.
Proof.
  pose (origins :=
  list_player_pieces (board st) (chess_to_play st)).
  eapply flat_map.
  2:{ eauto. }
  intros [pos p].
  eapply map.
  intro.
  constructor.
  - exact p.
  - exact pos.
  - exact X.
  - refine (filter (fun pos' =>
      (openb (chess_to_play st) (board st)) pos' &&
      _)
      (candidate_destinations p st pos)).
    pose (updated_board :=
      clear pos (place_piece (chess_to_play st) p pos' (board st))).
    pose (new_king :=
      match p with
      | King => pos'
      | _ => king st (chess_to_play st)
      end).
    exact (negb (is_threatened_byb updated_board new_king (opp (chess_to_play st)))).
Defined.

Lemma get_PreMoves_legal st :
  forall pm, In pm (get_PreMoves st) -> legal st pm.
Proof.
  intros pm pf.
  unfold get_PreMoves in pf.
  rewrite in_flat_map in pf.
  destruct pf as [[pos p] [H1 H2]].
  rewrite in_map_iff in H2.
  destruct H2 as [pos' [? H2]]; subst.
  rewrite filter_In in H2; destruct H2 as [H2 H3].
  rewrite andb_true_iff in H3.
  destruct H3 as [H3 H4].
  constructor; simpl.
  - apply pre_move_origins_correct; auto.
  - rewrite openb_iff in H3; auto.
  - apply candidate_destinations_correct1; auto.
  - intros.
    intro pf.
    rewrite is_threatened_byb_iff in pf.
    assert (pos0 =
      match p with
          | King => pos'
          | _ => king st (chess_to_play st)
          end).
    { destruct (eq_dec p King).
      + rewrite e.
        subst.
        destruct (eq_dec pos0 pos).
        ++ subst.
           rewrite lookup_clear_eq in H.
           discriminate.
        ++ rewrite lookup_clear_neq in H; auto.
           destruct (eq_dec pos0 pos'); auto.
           rewrite lookup_place_neq in H; auto.
           apply st in H.
           assert (pos = king st (chess_to_play st)); [|congruence].
           apply st.
           apply list_player_pieces_correct2 in H1; auto.
      + transitivity (king st (chess_to_play st)).
        * apply st.
          destruct (eq_dec pos0 pos).
          -- subst.
             rewrite lookup_clear_eq in H.
             discriminate.
          -- rewrite lookup_clear_neq in H; auto.
             destruct (eq_dec pos0 pos').
             ++ subst.
                rewrite lookup_place_eq in H.
                elim n; now inversion H.
             ++ rewrite lookup_place_neq in H; auto.
        * destruct p; (reflexivity || contradiction).
    }
    subst.
    rewrite pf in H4; discriminate.
Qed.

Lemma lookup_king st : forall pl,
  lookup_piece (king st pl) (board st) = Some (pl, King).
Proof.
  destruct pl; apply st.
Qed.

Lemma legal_get_PreMoves {st} {pm} :
  legal st pm -> In pm (get_PreMoves st).
Proof.
  intro l.
  unfold get_PreMoves.
  rewrite in_flat_map.
  exists (origin pm, piece pm); split.
  - rewrite list_player_pieces_correct.
    apply l.
  - rewrite in_map_iff.
    exists (dest pm).
    split.
    + destruct pm; reflexivity.
    + rewrite filter_In; split.
      * apply candidate_destinations_correct2.
        apply l.
      * apply andb_true_intro; split.
        -- rewrite openb_iff.
           apply l.
        -- rewrite negb_true_iff.
           rewrite <- is_threatened_byb_false_iff.
           intro thr.
           destruct thr as [pos' [pc [H1 H2]]].
           elim l; intros.
           elim (no_resulting_check0 (
             match piece pm with
             | King => dest pm
             | _ => king st (chess_to_play st)
             end)).
           ++ destruct (eq_dec (piece pm) King).
              ** rewrite e.
                 unfold updated_board0.
                 rewrite lookup_clear_neq;
                 [| apply (dest_orig_neq (Build_RegularMove st pm l))].
                 rewrite lookup_place_eq.
                 repeat f_equal; auto.
              ** transitivity (lookup_piece
                   (king st (chess_to_play st))
                   updated_board0).
                 --- destruct (piece pm); (reflexivity || contradiction).
                 --- unfold updated_board0.
                     rewrite lookup_clear_neq.
                     +++ rewrite lookup_place_neq.
                         *** apply lookup_king.
                         *** intro pf.
                             unfold open in dest_open0.
                             rewrite <- pf in dest_open0.
                             rewrite lookup_king in dest_open0.
                             elim (opp_no_fp (chess_to_play st)); auto.
                     +++ intro pf; apply n.
                         rewrite <- pf in origin_lookup0.
                         rewrite lookup_king in origin_lookup0.
                         now inversion origin_lookup0.
           ++ exists pos', pc; split; auto.
Qed.

Fixpoint map_pfs {X Y} (xs : list X) {struct xs} : (forall x : X, In x xs -> Y) -> list Y :=
  match xs with
  | [] => fun _ => []
  | x :: ys => fun f =>
    f x (or_introl eq_refl) ::
    map_pfs ys (fun y pf => f y (or_intror pf))
  end.

Definition enum_reg_moves (st : ChessState) : list (RegularMove st) :=
  map_pfs (get_PreMoves st) (fun pm pf => {|
    premove := pm;
    premove_legal := get_PreMoves_legal st pm pf
  |}).

Lemma in_map_pfs {X Y} (xs : list X) (f : forall x, In x xs -> Y) : forall (x : X) (pf : In x xs) y,
  f x pf = y ->
  In y (map_pfs xs f).
Proof.
  induction xs; intros x pf y Hy; subst.
  - destruct pf.
  - destruct pf; [subst|].
    + left; auto.
    + right.
      apply IHxs with (x := x) (pf := i).
      reflexivity.
Qed.

Lemma enum_reg_moves_all {st} : forall (m : RegularMove st),
  In m (enum_reg_moves st).
Proof.
  intro m.
  destruct m as [pm pf].
  unfold enum_reg_moves.
  apply in_map_pfs with
    (x := pm)
    (pf := legal_get_PreMoves pf).
  f_equal.
  apply UIP.
Qed.

Definition enum_chess_moves (st : ChessState) : list (ChessMove st) :=
  map (reg_move st) (enum_reg_moves st).

Lemma enum_chess_moves_all {st} : forall (m : ChessMove st),
  In m (enum_chess_moves st).
Proof.
  intro m.
  destruct m.
  apply in_map.
  apply enum_reg_moves_all.
Qed.

Definition in_check (s : ChessState) : Prop := forall pos,
  lookup_piece pos (board s) = Some (chess_to_play s, King) ->
  is_threatened_by (board s) pos (opp (chess_to_play s)).

Definition atomic_chess_res : ChessState -> option Result :=
  fun s =>
    match enum_chess_moves s with
    | nil =>
      match dec (P := in_check s) with
      | left _ => Some (Win (opp (chess_to_play s)))
      | right _ => Some Draw
      end
    | _ => None
    end.

Definition ChessGame : Game. refine ( {|
  GameState := ChessState;
  Move := ChessMove;

  to_play := chess_to_play;
  exec_move := @exec_ChessMove;

  atomic_res := atomic_chess_res;
  enum_moves := enum_chess_moves;

  enum_all := @enum_chess_moves_all;
  to_play_exec_move := @chess_to_play_exec_ChessMove;
  atomic_res_nil := _;
  nil_atomic_res := _
  |} ).
Proof.
  { unfold atomic_chess_res; intros.
    destruct (enum_chess_moves b); [auto|discriminate].
  }
  { intros.
    unfold atomic_chess_res.
    rewrite H.
    destruct dec; eexists; auto.
  }
Defined.
