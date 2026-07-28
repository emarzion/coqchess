Require Import Bool.
Import BoolNotations.
Require Import Lia.
Require Import List.
Import ListNotations.
Require Import Wellfounded.

Require Import Games.Game.Player.
Require Import Games.Game.Game.
Require Import Games.Util.Dec.

Require Import Chess.Util.Mat.
Require Import Chess.Util.Fin.
Require Import Chess.Util.UIP.
Require Import Chess.Util.ListUtil.

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

Definition is_threatened_by_piece : Board -> Pos -> Player -> Piece -> Prop :=
  fun b pos player piece =>
    exists pos',
      pos <> pos' /\
      lookup_piece pos' b = Some (player, piece) /\
      non_pawn_piece_adj piece b pos' pos.

Definition is_threatened_by : Board -> Pos -> Player -> Prop :=
  fun b pos player =>
    exists piece, is_threatened_by_piece b pos player piece.

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
    exists (piece (premove m)), (origin (premove m)).
    repeat split.
    + apply dest_orig_neq.
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

Fixpoint Fin_coerce {n} : nat -> option (Fin n) :=
  match n with
  | 0 => fun _ => None
  | S m => fun i =>
    match i with
    | 0 => Some (inl tt)
    | S j => option_map inr ((Fin_coerce j) : option (Fin m))
    end
  end.

Definition above {n} (i : Fin n) (k : nat) : option (Fin n) :=
  Fin_coerce (val i + k).

Definition below {n} (i : Fin n) (k : nat) : option (Fin n) :=
  if Compare_dec.lt_dec (val i) k then None else
  Fin_coerce (val i - k).

Definition circle {n} (i : Fin n) (r : nat) :
  list (Fin n) :=
  match r with
  | 0 => [i]
  | _ => filter_Some [above i r; below i r]
  end.

Lemma filter_Some_iff {X} (xs : list (option X)) :
  forall x, In x (filter_Some xs) <-> In (Some x) xs.
Proof.
  intro x; split.
  - induction xs as [|[x'|] ys].
    + intros [].
    + intros [|].
      * left; congruence.
      * right; now apply IHys.
    + intro.
      right; now apply IHys.
  - induction xs as [|[x'|] ys].
    + intros [].
    + intros [|].
      * left; congruence.
      * right; now apply IHys.
    + intros [|]; [discriminate|].
      now apply IHys.
Qed.

Lemma dist_plus m : forall n k,
  Dist.dist m n = k ->
  m = n + k \/
  n = m + k.
Proof.
  induction m; intros n k pf.
  - now right.
  - simpl in pf.
    destruct n.
    + now left.
    + apply IHm in pf.
      lia.
Qed.

Lemma Fin_coerce_val {n} (i : Fin n) :
  Fin_coerce (val i) = Some i.
Proof.
  induction n.
  - destruct i.
  - destruct i as [[]|j].
    + auto.
    + simpl; now rewrite IHn.
Qed.

Lemma val_Fin_coerce {n} (i : Fin n) : forall k,
  Fin_coerce k = Some i ->
  val i = k.
Proof.
  induction n; intros k pf.
  - destruct i.
  - destruct i as [[]|j].
    + simpl in pf.
      destruct k; auto.
      destruct (Fin_coerce k); discriminate.
    + simpl in pf.
      destruct k; [discriminate|].
      destruct (Fin_coerce k) eqn:Hk; [|discriminate].
      apply IHn in Hk. simpl.
      inversion pf; congruence.
Qed.

(* TODO: move from StateAction *)
Lemma dist_add m n :
  Dist.dist m (m + n) = n.
Proof.
  induction m; auto.
Qed.

Lemma dist_refl : forall n, Dist.dist n n = 0.
Proof.
  induction n; auto.
Qed.

Lemma dist_sub n : forall k, (k <= n)%nat ->
  Dist.dist n k = n - k.
Proof.
  induction n; intros k Hk.
  - simpl.
    inversion Hk; auto.
  - inversion Hk.
    + rewrite dist_refl.
      rewrite PeanoNat.Nat.sub_diag; auto.
    + destruct k.
      * reflexivity.
      * simpl.
        apply IHn.
        apply le_S_n; auto.
Qed.

Lemma circle_iff {n} (i : Fin n) r : forall j,
  fin_dist i j = r <->
  In j (circle i r).
Proof.
  intro j; split; intro pf.
  - destruct r.
    + apply fin_dist_0 in pf; now left.
    + apply filter_Some_iff.
      apply dist_plus in pf.
      destruct pf.
      * right; left.
        unfold below.
        rewrite H.
        destruct Compare_dec.lt_dec; [lia|].
        rewrite PeanoNat.Nat.add_sub.
        apply Fin_coerce_val.
      * left.
        unfold above.
        rewrite <- H.
        apply Fin_coerce_val.
  - destruct r.
    + destruct pf as [|[]]; subst.
      apply fin_dist_refl.
    + apply filter_Some_iff in pf.
      destruct pf as [pf|[pf|[]]].
      * unfold above in pf.
        apply val_Fin_coerce in pf.
        unfold fin_dist.
        rewrite pf.
        apply dist_add.
      * unfold below in pf.
        destruct Compare_dec.lt_dec; [discriminate|].
        apply val_Fin_coerce in pf.
        unfold fin_dist.
        rewrite pf.
        rewrite dist_sub; lia.
Qed.

Definition knight_neighbors (p : Pos) : list Pos :=
  list_prod (circle (fst p) 1) (circle (snd p) 2) ++
  list_prod (circle (fst p) 2) (circle (snd p) 1).

Lemma knight_neighbors_correct p p' :
  In p (knight_neighbors p') <->
  L_preadj p p'.
Proof.
  destruct p as [x y].
  unfold knight_neighbors.
  split; intro pf.
  - apply in_app_or in pf.
    destruct pf as [pf|pf].
    + rewrite in_prod_iff in pf.
      destruct pf as [pf1 pf2].
      rewrite <- circle_iff, fin_dist_sym in pf1, pf2.
      left; auto.
    + rewrite in_prod_iff in pf.
      destruct pf as [pf1 pf2].
      rewrite <- circle_iff, fin_dist_sym in pf1, pf2.
      right; auto.
  - apply in_or_app.
    destruct pf as [[pf1 pf2]|[pf1 pf2]].
    + rewrite file_dist_sym in pf1.
      rewrite rank_dist_sym in pf2.
      left.
      rewrite in_prod_iff; split; rewrite <- circle_iff; auto.
    + rewrite file_dist_sym in pf1.
      rewrite rank_dist_sym in pf2.
      right.
      rewrite in_prod_iff; split; rewrite <- circle_iff; auto.
Qed.

Definition decb P `{D : Dec P} : bool :=
  if @dec P D then true else false.

Definition is_threatened_by_knight
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  existsb (fun pos' =>
    if eq_dec (lookup_piece pos' b) (Some (pl, Knight)) then true else false)
  (knight_neighbors pos).

Lemma eq_dec_refl {X} `{Discrete X} x {Y} (y y' : Y) :
  (if eq_dec x x then y else y') = y.
Proof.
  destruct eq_dec; auto.
  contradiction.
Qed.

Lemma is_threatened_by_knight_iff b pos pl :
  is_threatened_by_piece b pos pl Knight <->
  is_threatened_by_knight b pos pl = true.
Proof.
  unfold is_threatened_by_knight.
  rewrite existsb_exists.
  split; intro pf.
  - destruct pf as [pos' [pf1 [pf2 pf3]]].
    simpl in pf3.
    rewrite <- knight_neighbors_correct in pf3.
    exists pos'; split; auto.
    rewrite pf2.
    now rewrite eq_dec_refl.
  - destruct pf as [pos' [pf1 pf2]].
    rewrite knight_neighbors_correct in pf1.
    destruct eq_dec; [|discriminate].
    exists pos'; split; auto.
    intros ?; subst.
    destruct pf1 as [[pf1 _]|[pf1 _]].
    + unfold file_dist in pf1.
      rewrite fin_dist_refl in pf1; lia.
    + unfold file_dist in pf1.
      rewrite fin_dist_refl in pf1; lia.
Qed.

Definition king_neighbors (p : Pos) : list Pos :=
  let fs := fst p :: circle (fst p) 1 in
  let rs := snd p :: circle (snd p) 1 in
  list_prod fs rs.

Lemma king_neighbors_correct p p' :
  In p (king_neighbors p') <->
  neighbor_preadj p p'.
Proof.
  destruct p as [x y].
  unfold Pos, File, Rank.
  unfold king_neighbors.
  split; intro pf.
  - rewrite in_prod_iff in pf.
    destruct pf as [pf1 pf2].
    split; unfold file_dist, rank_dist, rank,
      file; simpl.
    + destruct pf2.
      * subst.
        rewrite fin_dist_refl; lia.
      * rewrite <- circle_iff in H.
        rewrite fin_dist_sym; lia.
    + destruct pf1.
      * subst.
        rewrite fin_dist_refl; lia.
      * rewrite <- circle_iff in H.
        rewrite fin_dist_sym; lia.
  - destruct pf as [pf1 pf2].
    unfold rank_dist, file_dist, rank, file in *;
      simpl in pf1, pf2.
    rewrite PeanoNat.Nat.le_1_r in pf1, pf2.
    rewrite in_prod_iff; split.
    + destruct pf2.
      * apply fin_dist_0 in H; subst.
        now left.
      * right; rewrite fin_dist_sym in H.
        rewrite <- circle_iff; auto.
    + destruct pf1.
      * apply fin_dist_0 in H; subst.
        now left.
      * right; rewrite fin_dist_sym in H.
        rewrite <- circle_iff; auto.
Qed.

Definition is_threatened_by_king
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  existsb (fun pos' =>
    if eq_dec (lookup_piece pos' b) (Some (pl, King)) then true else false)
  (filter (fun p' => negb (if eq_dec pos p' then true else false))
  (king_neighbors pos)).

Lemma is_threatened_by_king_iff b pos pl :
  is_threatened_by_piece b pos pl King <->
  is_threatened_by_king b pos pl = true.
Proof.
  unfold is_threatened_by_king.
  rewrite existsb_exists.
  split; intro pf.
  - destruct pf as [pos' [pf1 [pf2 pf3]]].
    simpl in pf3.
    unfold neighbor_adj in pf3.
    rewrite <- king_neighbors_correct in pf3.
    exists pos'; split; auto.
    + rewrite filter_In; split; auto.
      destruct eq_dec; auto.
    + rewrite pf2; now rewrite eq_dec_refl.
  - destruct pf as [pos' [pf1 pf2]].
    rewrite filter_In in pf1.
    destruct pf1 as [pf1 pf3].
    rewrite king_neighbors_correct in pf1.
    destruct (eq_dec pos pos'); [discriminate|].
    destruct eq_dec; [|discriminate].
    exists pos'; split; auto.
Qed.

Definition rel_of_opt {X} (f : X -> option X) :
  X -> X -> Prop :=
  fun x x' => f x' = Some x.

Definition add_opt_pf {X} (f : X -> option X) (x : X) :
  option { y : X & rel_of_opt f y x } :=
 match f x as o return option {y : X & o = Some y} with
 | Some y => Some (existT _ y eq_refl)
 | None => None
 end.

Lemma add_opt_pf_None {X} (f : X -> option X) (x : X) :
  add_opt_pf f x = None ->
  f x = None.
Proof.
  refine (
    match f x as fx return
      (match fx as o return option { y : X & o = Some y } with
       | Some y => Some (existT _ y eq_refl)
       | None => None
       end = None ->
       fx = None)
    with
    | Some y => _
    | None => _
    end).
  - intros; discriminate.
  - intros; auto.
Qed.

Fixpoint find_first {X} (p : X -> bool)
  (f : X -> option X) (x0 : X) (a : Acc (rel_of_opt f) x0) : option X :=
  match a with
  | Acc_intro _ accs =>
    match p x0 with
    | true => Some x0
    | false =>
      match add_opt_pf f x0 with
      | Some (existT _ y pf) => find_first p f y (accs _ pf)
      | None => None
      end
    end
  end.

Fixpoint find_first_pred {X} (p : X -> bool) (f : X -> option X)
  (x0 : X) (a : Acc (rel_of_opt f) x0) y {struct a} :
  find_first p f x0 a = Some y -> p y = true.
Proof.
  destruct a as [accs]; intro pf.
  unfold find_first in pf.
  destruct (p x0) eqn:px0.
  - congruence.
  - destruct add_opt_pf as [[z Hz]|].
    + now apply find_first_pred in pf.
    + discriminate.
Qed.

Fixpoint opt_iter {X} (f : X -> option X) (n : nat) (x0 : X) : option X :=
  match n with
  | 0 => Some x0
  | S m =>
    match f x0 with
    | Some x1 => opt_iter f m x1
    | None => None
    end
  end.

Fixpoint find_first_is_first {X} (p : X -> bool) (f : X -> option X)
  (x0 : X) (a : Acc (rel_of_opt f) x0) y {struct a} :
  find_first p f x0 a = Some y ->
  exists n, opt_iter f n x0 = Some y /\
  forall k z, (k < n)%nat -> opt_iter f k x0 = Some z ->
    p z = false.
Proof.
  destruct a as [accs]; intro pf.
  simpl in pf.
  destruct (p x0) eqn:px0.
  - exists 0; split; auto.
    intros; lia.
  - destruct add_opt_pf as [[z Hz]|].
    + unfold rel_of_opt in Hz.
      apply find_first_is_first in pf.
      destruct pf as [n [Hn1 Hn2]].
      exists (S n); split.
      * simpl.
        rewrite Hz; auto.
      * intros.
        destruct k.
        -- inversion H0.
           congruence.
        -- simpl in H0.
           rewrite Hz in H0.
           apply Hn2 in H0; auto.
           lia.
    + discriminate.
Qed.

Fixpoint find_first_None {X} (p : X -> bool) (f : X -> option X)
  (x0 : X) (a : Acc (rel_of_opt f) x0) {struct a} :
  find_first p f x0 a = None ->
  forall n y, opt_iter f n x0 = Some y -> p y = false.
Proof.
  destruct a as [accs]; intros pf n y Hy.
  simpl in pf.
  destruct (p x0) eqn:px0; [discriminate|].
  destruct add_opt_pf as [[z Hz]|] eqn:Hadd_opt.
  - destruct n as [|m].
    + inversion Hy; congruence.
    + simpl in Hy.
      unfold rel_of_opt in Hz.
      rewrite Hz in Hy.
      apply find_first_None with (n := m) (y := y) in pf; auto.
  - destruct n.
    + inversion Hy; congruence.
    + simpl in Hy.
      destruct (f x0) eqn:fx0; [|discriminate].
      apply add_opt_pf_None in Hadd_opt.
      rewrite Hadd_opt in fx0.
      discriminate.
Qed.

Definition is_orthog_threatened b pos pl :=
  exists pos',
    pos <> pos' /\ (
    lookup_piece pos' b = Some (pl, Rook) \/
    lookup_piece pos' b = Some (pl, Queen)
  ) /\
  orthog_adj b pos' pos.

Definition north (p : Pos) : option Pos :=
  match next (snd p) with
  | Some r => Some (fst p, r)
  | None => None
  end.

Definition south (p : Pos) : option Pos :=
  match prev (snd p) with
  | Some r => Some (fst p, r)
  | None => None
  end.

Definition east (p : Pos) : option Pos :=
  match next (fst p) with
  | Some r => Some (r, snd p)
  | None => None
  end.

Definition west (p : Pos) : option Pos :=
  match prev (fst p) with
  | Some r => Some (r, snd p)
  | None => None
  end.

Definition northeast (p : Pos) : option Pos :=
  match north p with
  | Some p' =>
    match east p' with
    | Some p'' => Some p''
    | None => None
    end
  | None => None
  end.

Definition southeast (p : Pos) : option Pos :=
  match south p with
  | Some p' =>
    match east p' with
    | Some p'' => Some p''
    | None => None
    end
  | None => None
  end.

Definition northwest (p : Pos) : option Pos :=
  match north p with
  | Some p' =>
    match west p' with
    | Some p'' => Some p''
    | None => None
    end
  | None => None
  end.

Definition southwest (p : Pos) : option Pos :=
  match south p with
  | Some p' =>
    match west p' with
    | Some p'' => Some p''
    | None => None
    end
  | None => None
  end.

Lemma next_val_Some {n} (i j : Fin n) :
  next i = Some j -> val j = S (val i).
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i as [[]|i'].
    simpl in pf.
    + destruct n; [discriminate|].
      inversion pf; auto.
    + simpl in pf.
      destruct next eqn:Hnext; [|discriminate].
      apply IHn in Hnext.
      inversion pf; simpl.
      now rewrite Hnext.
Qed.

Lemma prev_val_None {n} (i : Fin n) :
  prev i = None -> val i = 0.
Proof.
  destruct n; intro pf.
  - destruct i.
  - destruct i as [[]|j].
    + auto.
    + simpl in pf.
      destruct (prev j); discriminate.
Qed.

Lemma prev_val_Some {n} (i j : Fin n) :
  prev i = Some j -> S (val j) = val i.
Proof.
  induction n; intro pf.
  - destruct i.
  - destruct i as [[]|i'].
    simpl in pf.
    + destruct n; [discriminate|].
      inversion pf; auto.
    + simpl in pf.
      destruct prev eqn:Hprev.
      * apply IHn in Hprev.
        inversion pf; simpl.
        now rewrite Hprev.
      * apply prev_val_None in Hprev.
        inversion pf; subst.
        simpl; congruence.
Qed.

Lemma next_val_None {n} (i : Fin n) :
  next i = None -> forall (j : Fin n),
  (val j <= val i)%nat.
Proof.
  induction n; intros pf j.
  - destruct i.
  - destruct i as [[]|i'].
    + simpl in pf.
      destruct n; [|discriminate].
      now destruct j as [[]|[]].
    + simpl in *.
      destruct next eqn:Hnext.
      * destruct j; [lia|discriminate].
      * destruct j; [lia|].
        apply IHn with (j := f) in Hnext.
        lia.
Qed.

Lemma iter_north_Some n p p' :
  opt_iter north n p = Some p' <->
  fst p' = fst p /\
  val (snd p') = val (snd p) + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct north eqn:Hnorth; [|discriminate].
      unfold north in Hnorth.
      destruct next eqn:Hnext; [|discriminate].
      apply next_val_Some in Hnext.
      inversion Hnorth; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      split; auto.
      rewrite H0; simpl snd; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in pf2.
      apply val_inj in pf2.
      apply injective_projections; auto.
    + simpl.
      destruct north eqn:Hnorth.
      * unfold north in Hnorth.
        destruct next eqn:Hnext; [|discriminate].
        inversion Hnorth; subst.
        apply IHn; split; auto.
        apply next_val_Some in Hnext.
        simpl snd; lia.
      * unfold north in Hnorth.
        destruct next eqn:Hnext; [discriminate|].
        apply next_val_None with (j := snd p')
          in Hnext; lia.
Qed.

Lemma iter_east_Some n p p' :
  opt_iter east n p = Some p' <->
  snd p' = snd p /\
  val (fst p') = val (fst p) + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct east eqn:Heast; [|discriminate].
      unfold east in Heast.
      destruct next eqn:Hnext; [|discriminate].
      apply next_val_Some in Hnext.
      inversion Heast; subst.
      apply IHn in pf; simpl snd in *; destruct pf.
      split; auto.
      rewrite H0; simpl fst; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in pf2.
      apply val_inj in pf2.
      apply injective_projections; auto.
    + simpl.
      destruct east eqn:Heast.
      * unfold east in Heast.
        destruct next eqn:Hnext; [|discriminate].
        inversion Heast; subst.
        apply IHn; split; auto.
        apply next_val_Some in Hnext.
        simpl fst; lia.
      * unfold east in Heast.
        destruct next eqn:Hnext; [discriminate|].
        apply next_val_None with (j := fst p')
          in Hnext; lia.
Qed.

Lemma iter_south_Some n p p' :
  opt_iter south n p = Some p' <->
  fst p' = fst p /\
  val (snd p) = val (snd p') + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct south eqn:Hsouth; [|discriminate].
      unfold south in Hsouth.
      destruct prev eqn:Hprev; [|discriminate].
      apply prev_val_Some in Hprev.
      inversion Hsouth; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      split; auto.
      simpl snd in *; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in pf2.
      apply val_inj in pf2.
      apply injective_projections; auto.
    + simpl.
      destruct south eqn:Hsouth.
      * unfold south in Hsouth.
        destruct prev eqn:Hprev; [|discriminate].
        inversion Hsouth; subst.
        apply IHn; split; auto.
        apply prev_val_Some in Hprev.
        simpl snd; lia.
      * unfold south in Hsouth.
        destruct prev eqn:Hprev; [discriminate|].
        apply prev_val_None in Hprev; lia.
Qed.

Lemma iter_west_Some n p p' :
  opt_iter west n p = Some p' <->
  snd p' = snd p /\
  val (fst p) = val (fst p') + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct west eqn:Hwest; [|discriminate].
      unfold west in Hwest.
      destruct prev eqn:Hprev; [|discriminate].
      apply prev_val_Some in Hprev.
      inversion Hwest; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      split; auto.
      simpl snd in *; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in pf2.
      apply val_inj in pf2.
      apply injective_projections; auto.
    + simpl.
      destruct west eqn:Hwest.
      * unfold west in Hwest.
        destruct prev eqn:Hprev; [|discriminate].
        inversion Hwest; subst.
        apply IHn; split; auto.
        apply prev_val_Some in Hprev.
        simpl fst; lia.
      * unfold west in Hwest.
        destruct prev eqn:Hprev; [discriminate|].
        apply prev_val_None in Hprev; lia.
Qed.

Lemma iter_ne_Some n p p' :
  opt_iter northeast n p = Some p' <->
  val (fst p') = val (fst p) + n /\
  val (snd p') = val (snd p) + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct northeast eqn:Hne; [|discriminate].
      unfold northeast, north, east in Hne.
      destruct (next (snd p)) eqn:Hnext2; [|discriminate].
      simpl fst in Hne.
      destruct (next (fst p)) eqn:Hnext1; [|discriminate].
      simpl snd in Hne.
      apply next_val_Some in Hnext1, Hnext2.
      inversion Hne; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      simpl snd in *; split; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in *.
      apply val_inj in pf1, pf2.
      apply injective_projections; auto.
    + simpl.
      destruct northeast eqn:Hne.
      * unfold northeast, north, east in Hne.
        destruct (next (snd p)) eqn:Hnext2; [|discriminate].
        simpl fst in Hne.
        destruct (next (fst p)) eqn:Hnext1; [|discriminate].
        simpl snd in Hne.
        inversion Hne; subst.
        apply next_val_Some in Hnext1, Hnext2.
        apply IHn; split; simpl fst; simpl snd; lia.
      * unfold northeast, north, east in Hne.
        destruct (next (snd p)) eqn:Hnext1.
        -- simpl fst in Hne.
           destruct (next (fst p)) eqn:Hnext2; [discriminate|].
           apply next_val_None with (j := fst p') in Hnext2; lia.
        -- apply next_val_None with (j := snd p') in Hnext1; lia.
Qed.

Lemma iter_se_Some n p p' :
  opt_iter southeast n p = Some p' <->
  val (fst p') = val (fst p) + n /\
  val (snd p') + n = val (snd p).
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct southeast eqn:Hse; [|discriminate].
      unfold southeast, south, east in Hse.
      destruct (prev (snd p)) eqn:Hprev2; [|discriminate].
      simpl fst in Hse.
      destruct (next (fst p)) eqn:Hnext1; [|discriminate].
      simpl snd in Hse.
      apply next_val_Some in Hnext1.
      apply prev_val_Some in Hprev2.
      inversion Hse; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      simpl snd in *; split; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in *.
      apply val_inj in pf1, pf2.
      apply injective_projections; auto.
    + simpl.
      destruct southeast eqn:Hse.
      * unfold southeast, south, east in Hse.
        destruct (prev (snd p)) eqn:Hprev2; [|discriminate].
        simpl fst in Hse.
        destruct (next (fst p)) eqn:Hnext1; [|discriminate].
        simpl snd in Hse.
        inversion Hse; subst.
        apply next_val_Some in Hnext1.
        apply prev_val_Some in Hprev2.
        apply IHn; split; simpl fst; simpl snd; lia.
      * unfold southeast, south, east in Hse.
        destruct (prev (snd p)) eqn:Hprev2.
        -- simpl fst in Hse.
           destruct (next (fst p)) eqn:Hnext2; [discriminate|].
           apply next_val_None with (j := fst p') in Hnext2; lia.
        -- apply prev_val_None in Hprev2; lia.
Qed.

Lemma iter_nw_Some n p p' :
  opt_iter northwest n p = Some p' <->
  val (fst p') + n = val (fst p) /\
  val (snd p') = val (snd p) + n.
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct northwest eqn:Hnw; [|discriminate].
      unfold northwest, north, west in Hnw.
      destruct (next (snd p)) eqn:Hnext2; [|discriminate].
      simpl fst in Hnw.
      destruct (prev (fst p)) eqn:Hprev1; [|discriminate].
      simpl snd in Hnw.
      apply prev_val_Some in Hprev1.
      apply next_val_Some in Hnext2.
      inversion Hnw; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      simpl snd in *; split; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in *.
      apply val_inj in pf1, pf2.
      apply injective_projections; auto.
    + simpl.
      destruct northwest eqn:Hnw.
      * unfold northwest, north, west in Hnw.
        destruct (next (snd p)) eqn:Hnext2; [|discriminate].
        simpl fst in Hnw.
        destruct (prev (fst p)) eqn:Hprev1; [|discriminate].
        simpl snd in Hnw.
        inversion Hnw; subst.
        apply prev_val_Some in Hprev1.
        apply next_val_Some in Hnext2.
        apply IHn; split; simpl fst; simpl snd; lia.
      * unfold northwest, north, west in Hnw.
        destruct (next (snd p)) eqn:Hnext2.
        -- simpl fst in Hnw.
           destruct (prev (fst p)) eqn:Hprev1; [discriminate|].
           apply prev_val_None in Hprev1; lia.
        -- apply next_val_None with (j := snd p') in Hnext2; lia.
Qed.

Lemma iter_sw_Some n p p' :
  opt_iter southwest n p = Some p' <->
  val (fst p') + n = val (fst p) /\
  val (snd p') + n = val (snd p).
Proof.
  split; generalize p p'; clear p p'.
  - induction n; intros p p' pf.
    + inversion pf; subst.
      rewrite <- plus_n_O; now split.
    + simpl in pf.
      destruct southwest eqn:Hsw; [|discriminate].
      unfold southwest, south, west in Hsw.
      destruct (prev (snd p)) eqn:Hprev2; [|discriminate].
      simpl fst in Hsw.
      destruct (prev (fst p)) eqn:Hprev1; [|discriminate].
      simpl snd in Hsw.
      apply prev_val_Some in Hprev1, Hprev2.
      inversion Hsw; subst.
      apply IHn in pf; simpl fst in *; destruct pf.
      simpl snd in *; split; lia.
  - induction n; intros p p' [pf1 pf2].
    + simpl; f_equal.
      rewrite <- plus_n_O in *.
      apply val_inj in pf1, pf2.
      apply injective_projections; auto.
    + simpl.
      destruct southwest eqn:Hsw.
      * unfold southwest, south, west in Hsw.
        destruct (prev (snd p)) eqn:Hprev2; [|discriminate].
        simpl fst in Hsw.
        destruct (prev (fst p)) eqn:Hprev1; [|discriminate].
        simpl snd in Hsw.
        inversion Hsw; subst.
        apply prev_val_Some in Hprev1, Hprev2.
        apply IHn; split; simpl fst; simpl snd; lia.
      * unfold southwest, south, west in Hsw.
        destruct (prev (snd p)) eqn:Hprev1.
        -- simpl fst in Hsw.
           destruct (prev (fst p)) eqn:Hprev2; [discriminate|].
           apply prev_val_None in Hprev2; lia.
        -- apply prev_val_None in Hprev1; lia.
Qed.

Lemma wf_north : well_founded (rel_of_opt north).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_gt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold north in pf.
    destruct (next _) eqn:Hnext; inversion pf; simpl.
    apply next_val_Some in Hnext.
    unfold Fin_gt; rewrite Hnext.
    unfold Rank; simpl; lia.
  - apply wf_inverse_image; exact Fin_gt_wf.
Qed.

Lemma wf_east : well_founded (rel_of_opt east).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_gt (fst p) (fst p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold east in pf.
    destruct (next _) eqn:Hnext; inversion pf; simpl.
    apply next_val_Some in Hnext.
    unfold Fin_gt; rewrite Hnext.
    unfold File; simpl; lia.
  - apply wf_inverse_image; exact Fin_gt_wf.
Qed.

Lemma wf_south : well_founded (rel_of_opt south).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_lt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold south in pf.
    destruct (prev _) eqn:Hprev; inversion pf; simpl.
    apply prev_val_Some in Hprev.
    unfold Fin_lt; unfold Pos, File, Rank in *.
    simpl Fin in *; lia.
  - apply wf_inverse_image; exact Fin_lt_wf.
Qed.

Lemma wf_west : well_founded (rel_of_opt west).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_lt (fst p) (fst p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold west in pf.
    destruct (prev _) eqn:Hprev; inversion pf; simpl.
    apply prev_val_Some in Hprev.
    unfold Fin_lt; unfold Pos, File, Rank in *.
    simpl Fin in *; lia.
  - apply wf_inverse_image; exact Fin_lt_wf.
Qed.

Lemma wf_ne : well_founded (rel_of_opt northeast).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_gt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold northeast in pf.
    destruct (north p') eqn:Hnorth; [|discriminate].
    destruct (east p0) eqn:Heast; [|discriminate].
    inversion pf; subst.
    unfold north in Hnorth.
    destruct next eqn:Hnext2; [|discriminate].
    unfold east in Heast.
    destruct (next (fst p0)) eqn:Hnext1;
      [|discriminate].
    apply next_val_Some in Hnext1, Hnext2.
    unfold Fin_gt.
    inversion Hnorth; subst.
    simpl fst in *; simpl snd in *.
    inversion Heast; subst.
    simpl snd. rewrite Hnext2.
    apply Arith_base.gt_Sn_n_stt.
  - apply wf_inverse_image; exact Fin_gt_wf.
Qed.

Lemma wf_se : well_founded (rel_of_opt southeast).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_lt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold southeast in pf.
    destruct (south p') eqn:Hsouth; [|discriminate].
    destruct (east p0) eqn:Heast; [|discriminate].
    inversion pf; subst.
    unfold south in Hsouth.
    destruct prev eqn:Hprev2; [|discriminate].
    unfold east in Heast.
    destruct (next (fst p0)) eqn:Hnext1;
      [|discriminate].
    apply next_val_Some in Hnext1.
    apply prev_val_Some in Hprev2.
    unfold Fin_lt.
    inversion Hsouth; subst.
    simpl fst in *; simpl snd in *.
    inversion Heast; subst.
    simpl snd.
    unfold File, Rank, Fin in *.
    rewrite <- Hprev2.
    apply Arith_base.gt_Sn_n_stt.
  - apply wf_inverse_image; exact Fin_lt_wf.
Qed.

Lemma wf_nw : well_founded (rel_of_opt northwest).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_gt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold northwest in pf.
    destruct (north p') eqn:Hnorth; [|discriminate].
    destruct (west p0) eqn:Hwest; [|discriminate].
    inversion pf; subst.
    unfold north in Hnorth.
    destruct next eqn:Hnext2; [|discriminate].
    unfold west in Hwest.
    destruct (prev (fst p0)) eqn:Hprev1;
      [|discriminate].
    apply prev_val_Some in Hprev1.
    apply next_val_Some in Hnext2.
    unfold Fin_gt.
    inversion Hnorth; subst.
    simpl fst in *; simpl snd in *.
    inversion Hwest; subst.
    simpl snd. rewrite Hnext2.
    apply Arith_base.gt_Sn_n_stt.
  - apply wf_inverse_image; exact Fin_gt_wf.
Qed.

Lemma wf_sw : well_founded (rel_of_opt southwest).
Proof.
  apply wf_incl with (R2 := fun p p' => Fin_lt (snd p) (snd p')).
  - intros p p' pf.
    unfold rel_of_opt in pf.
    unfold southwest in pf.
    destruct (south p') eqn:Hsouth; [|discriminate].
    destruct (west p0) eqn:Hwest; [|discriminate].
    inversion pf; subst.
    unfold south in Hsouth.
    unfold Rank, File, Pos in *.
    destruct (prev (snd p')) eqn:Hprev2; [|discriminate].
    unfold west in Hwest.
    destruct (prev (fst p0)) eqn:Hprev1;
      [|discriminate].
    apply prev_val_Some in Hprev1, Hprev2.
    unfold Fin_lt.
    inversion Hsouth; subst.
    simpl fst in *; simpl snd in *.
    inversion Hwest; subst.
    simpl snd; lia.
  - apply wf_inverse_image; exact Fin_lt_wf.
Qed.

Definition neqb {X} `{Discrete X} : X -> X -> bool :=
  fun x y =>
    if eq_dec x y then false else true.

Definition is_north_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) north pos (wf_north pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Rook | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_east_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) east pos (wf_east pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Rook | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_south_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) south pos (wf_south pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Rook | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_west_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) west pos (wf_west pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Rook | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_orthog_threatenedb
  (b : Board) (pos : Pos) (pl : Player) : bool :=
     is_north_threatened b pos pl
  || is_south_threatened b pos pl
  || is_east_threatened b pos pl
  || is_west_threatened b pos pl.

Lemma le_diff {x y : nat} :
  (x <= y)%nat ->
  exists z, x + z = y.
Proof.
  intro; exists (y - x); lia.
Qed.

Lemma lt_diff {x y : nat} :
  (x < y)%nat ->
  exists z, x + z = y.
Proof.
  intro; exists (y - x); lia.
Qed.

Lemma is_north_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Rook) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  vert_adj b pos' pos ->
  (val (snd pos) <= val (snd pos'))%nat ->
  is_north_threatened b pos pl = true.
Proof.
  intros Hneq look pf_v Hle.
   destruct (le_diff Hle) as [d Hd].
   unfold is_north_threatened.
   destruct pf_v as [file_eq no_betw].
   destruct find_first eqn:Hfind.
   - pose proof (Hfind' := Hfind).
     apply find_first_is_first in Hfind.
     destruct Hfind as [n [Hn1 Hn2]].
     rewrite iter_north_Some in Hn1.
     destruct Hn1 as [Hf Hr].
     assert (n = d).
     { destruct (PeanoNat.Nat.lt_trichotomy n d)
         as [nd|[nd|nd]]; auto.
       + apply find_first_pred in Hfind'.
         rewrite no_betw in Hfind'; [discriminate| |].
         * unfold vert_preadj in *.
           unfold file in *; congruence.
         * right; unfold rank; split; [|lia].
           destruct (lookup_piece p b); [|discriminate].
           unfold neqb in Hfind'.
           destruct eq_dec; [discriminate|].
           destruct n; [|lia].
           elim n0.
           apply injective_projections; auto.
           rewrite <- plus_n_O  in Hr.
           now apply val_inj.
       + apply Hn2 with (z := pos') in nd.
         * destruct look as [look|look];
           rewrite look in nd.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
         * rewrite iter_north_Some; split; auto.
     }
     subst.
     assert (p = pos').
     { apply injective_projections.
       + rewrite Hf; auto.
       + rewrite Hd in Hr.
         now apply val_inj.
     }
     subst.
     destruct look as [look|look]; rewrite look;
             apply player_eqb_refl.
  - apply find_first_None with
            (n := d) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_north_Some.
      split; auto.
Qed.

Lemma is_east_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Rook) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  horiz_adj b pos' pos ->
  (val (fst pos) <= val (fst pos'))%nat ->
  is_east_threatened b pos pl = true.
Proof.
  intros Hneq look pf_h Hle.
   destruct (le_diff Hle) as [d Hd].
   unfold is_east_threatened.
   destruct pf_h as [rank_eq no_betw].
   destruct find_first eqn:Hfind.
   - pose proof (Hfind' := Hfind).
     apply find_first_is_first in Hfind.
     destruct Hfind as [n [Hn1 Hn2]].
     rewrite iter_east_Some in Hn1.
     destruct Hn1 as [Hf Hr].
     assert (n = d).
     { destruct (PeanoNat.Nat.lt_trichotomy n d) as [nd|[nd|nd]]; auto.
       + apply find_first_pred in Hfind'.
         rewrite no_betw in Hfind'; [discriminate| |].
         * unfold horiz_preadj in *.
           unfold rank in *; congruence.
          * right; unfold file; split; [|lia].
            destruct (lookup_piece p b); [|discriminate].
            unfold neqb in Hfind'.
            destruct eq_dec; [discriminate|].
            destruct n; [|lia].
            elim n0.
            apply injective_projections; auto.
            rewrite <- plus_n_O  in Hr.
            now apply val_inj.
       + apply Hn2 with (z := pos') in nd.
         * destruct look as [look|look];
           rewrite look in nd.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
         * rewrite iter_east_Some; split; auto.
     }
     subst.
     assert (p = pos').
     { apply injective_projections.
       + rewrite Hd in Hr.
         now apply val_inj.
       + rewrite Hf; auto.
     }
     subst.
     destruct look as [look|look]; rewrite look;
             apply player_eqb_refl.
  - apply find_first_None with
            (n := d) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_east_Some.
      split; auto.
Qed.

Lemma is_north_threatened_correct2 b pos pl :
  is_north_threatened b pos pl = true ->
  is_orthog_threatened b pos pl.
Proof.
  intro pf.
  unfold is_north_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    right; split.
    + rewrite iter_north_Some in Hd1.
      apply Hd1.
    + intros p' vert no_betw.
      destruct no_betw as [no_betw|no_betw].
      * rewrite iter_north_Some in Hd1.
        destruct Hd1.
        unfold rank in no_betw.
        destruct no_betw.
        rewrite H0 in H1. lia.
      * destruct no_betw as [nb1 nb2].
        destruct (lt_diff nb1) as [k Hk].
        specialize (Hd2 k p').
        destruct (lookup_piece p' b); [|auto].
        rewrite iter_north_Some in *.
        absurd (neqb p' pos = false).
        -- unfold neqb.
           destruct eq_dec; auto; subst; lia.
        -- apply Hd2.
           ++ destruct Hd1 as [_ Hd1].
              unfold rank in *; lia.
           ++ split; auto.
               unfold vert_preadj in vert.
               unfold file in vert.
               destruct Hd1; congruence.
Qed.

Lemma is_east_threatened_correct2 b pos pl :
  is_east_threatened b pos pl = true ->
  is_orthog_threatened b pos pl.
Proof.
  intro pf.
  unfold is_east_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    left; split.
    + rewrite iter_east_Some in Hd1.
      apply Hd1.
    + intros p' horiz no_betw.
      destruct no_betw as [no_betw|no_betw].
      * rewrite iter_east_Some in Hd1.
        destruct Hd1.
        unfold file in no_betw.
        destruct no_betw.
        rewrite H0 in H1. lia.
      * destruct no_betw as [nb1 nb2].
        destruct (lt_diff nb1) as [k Hk].
        specialize (Hd2 k p').
        destruct (lookup_piece p' b); [|auto].
        rewrite iter_east_Some in *.
        absurd (neqb p' pos = false).
        -- unfold neqb.
           destruct eq_dec; auto; subst; lia.
        -- apply Hd2.
           ++ destruct Hd1 as [_ Hd1].
              unfold file in *; lia.
           ++ split; auto.
               unfold horiz_preadj in horiz.
               unfold rank in horiz.
               destruct Hd1; congruence.
Qed.

Lemma is_south_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Rook) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  vert_adj b pos' pos ->
  (val (snd pos') <= val (snd pos))%nat ->
  is_south_threatened b pos pl = true.
Proof.
  intros Hneq look pf_v Hle.
  destruct (le_diff Hle) as [d Hd].
  unfold is_south_threatened.
  destruct pf_v as [file_eq no_betw].
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_south_Some in Hn1.
     destruct Hn1 as [Hf Hr].
     assert (n = d).
     { destruct (PeanoNat.Nat.lt_trichotomy n d) as [nd|[nd|nd]]; auto.
       + apply find_first_pred in Hfind'.
         rewrite no_betw in Hfind'; [discriminate| |].
         * unfold vert_preadj in *.
           unfold file in *; congruence.
          * left; unfold rank; split; [lia|].
            destruct (lookup_piece p b); [|discriminate].
            unfold neqb in Hfind'.
            destruct eq_dec; [discriminate|].
            destruct n; [|lia].
            elim n0.
            apply injective_projections; auto.
            rewrite <- plus_n_O  in Hr.
            now apply val_inj.
       + apply Hn2 with (z := pos') in nd.
         * destruct look as [look|look];
           rewrite look in nd.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
         * rewrite iter_south_Some; split; auto.
     }
     subst.
     assert (p = pos').
     { apply injective_projections.
       + rewrite Hf; auto.
       + rewrite <- Hd in Hr.
         apply val_inj; lia.
     }
     subst.
     destruct look as [look|look]; rewrite look;
             apply player_eqb_refl.
  - apply find_first_None with
            (n := d) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_south_Some.
      split; auto.
Qed.

Lemma is_west_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Rook) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  horiz_adj b pos' pos ->
  (val (fst pos') <= val (fst pos))%nat ->
  is_west_threatened b pos pl = true.
Proof.
  intros Hneq look pf_h Hle.
  destruct (le_diff Hle) as [d Hd].
  unfold is_west_threatened.
  destruct pf_h as [rank_eq no_betw].
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_west_Some in Hn1.
     destruct Hn1 as [Hf Hr].
     assert (n = d).
     { destruct (PeanoNat.Nat.lt_trichotomy n d) as [nd|[nd|nd]]; auto.
       + apply find_first_pred in Hfind'.
         rewrite no_betw in Hfind'; [discriminate| |].
         * unfold horiz_preadj in *.
           unfold rank in *; congruence.
          * left; unfold file; split; [lia|].
            destruct (lookup_piece p b); [|discriminate].
            unfold neqb in Hfind'.
            destruct eq_dec; [discriminate|].
            destruct n; [|lia].
            elim n0.
            apply injective_projections; auto.
            rewrite <- plus_n_O  in Hr.
            now apply val_inj.
       + apply Hn2 with (z := pos') in nd.
         * destruct look as [look|look];
           rewrite look in nd.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
           -- unfold neqb in nd.
              destruct eq_dec; [|discriminate].
              subst; contradiction.
         * rewrite iter_west_Some; split; auto.
     }
     subst.
     assert (p = pos').
     { apply injective_projections.
       + rewrite <- Hd in Hr.
         apply val_inj; lia.
       + rewrite Hf; auto.
     }
     subst.
     destruct look as [look|look]; rewrite look;
             apply player_eqb_refl.
  - apply find_first_None with
            (n := d) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_west_Some.
      split; auto.
Qed.

Lemma is_south_threatened_correct2 b pos pl :
  is_south_threatened b pos pl = true ->
  is_orthog_threatened b pos pl.
Proof.
  intro pf.
  unfold is_south_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    right; split.
    + rewrite iter_south_Some in Hd1.
      apply Hd1.
    + intros p' vert no_betw.
      destruct no_betw as [no_betw|no_betw].
      * destruct no_betw as [nb1 nb2].
        destruct (lt_diff nb2) as [k Hk].
        specialize (Hd2 k p').
        destruct (lookup_piece p' b); [|auto].
        rewrite iter_south_Some in *.
        absurd (neqb p' pos = false).
        -- unfold neqb.
           destruct eq_dec; auto; subst; lia.
        -- apply Hd2.
           ++ destruct Hd1 as [_ Hd1].
              unfold rank in *; lia.
           ++ split; auto.
               unfold vert_preadj in vert.
               unfold file in vert.
               destruct Hd1; congruence.
      * rewrite iter_south_Some in Hd1.
        destruct Hd1.
        unfold rank in no_betw.
        destruct no_betw.
        rewrite H0 in H1. lia.
Qed.

Lemma is_west_threatened_correct2 b pos pl :
  is_west_threatened b pos pl = true ->
  is_orthog_threatened b pos pl.
Proof.
  intro pf.
  unfold is_west_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    left; split.
    + rewrite iter_west_Some in Hd1.
      apply Hd1.
    + intros p' horiz no_betw.
      destruct no_betw as [no_betw|no_betw].
      * destruct no_betw as [nb1 nb2].
        destruct (lt_diff nb2) as [k Hk].
        specialize (Hd2 k p').
        destruct (lookup_piece p' b); [|auto].
        rewrite iter_west_Some in *.
        absurd (neqb p' pos = false).
        -- unfold neqb.
           destruct eq_dec; auto; subst; lia.
        -- apply Hd2.
           ++ destruct Hd1 as [_ Hd1].
              unfold file in *; lia.
           ++ split; auto.
               unfold horiz_preadj in horiz.
               unfold rank in horiz.
               destruct Hd1; congruence.
      * rewrite iter_west_Some in Hd1.
        destruct Hd1.
        unfold file in no_betw.
        destruct no_betw.
        rewrite H0 in H1. lia.
Qed.

Lemma is_orthog_threatened_iff b pos pl :
  is_orthog_threatened b pos pl <->
  is_orthog_threatenedb b pos pl = true.
Proof.
  split; intro pf.
  - destruct pf as [pos' [pf_neq [pf1 pf2]]].
    destruct pf2 as [pf_h|pf_v].
    + destruct (PeanoNat.Nat.le_ge_cases (val (fst pos))
        (val (fst pos'))) as [Hle|Hgt].
      (* East *)
      * unfold is_orthog_threatenedb.
        repeat rewrite orb_true_iff; left; right.
        apply is_east_threatened_correct1
          with (pos' := pos'); auto.
      (* West *)
      * unfold is_orthog_threatenedb.
        repeat rewrite orb_true_iff; right.
        apply is_west_threatened_correct1
          with (pos' := pos'); auto.
    + destruct (PeanoNat.Nat.le_ge_cases (val (snd pos))
        (val (snd pos'))) as [Hle|Hgt].
      (* North *)
      * unfold is_orthog_threatenedb.
        repeat rewrite orb_true_iff; left; left; left.
        apply is_north_threatened_correct1
          with (pos' := pos'); auto.
      (* South *)
      * unfold is_orthog_threatenedb.
        repeat rewrite orb_true_iff; left; left; right.
        apply is_south_threatened_correct1
          with (pos' := pos'); auto.
  - unfold is_orthog_threatenedb in pf.
    repeat rewrite orb_true_iff in pf.
    destruct pf as [[[|]|]|].
    + apply is_north_threatened_correct2; auto.
    + apply is_south_threatened_correct2; auto.
    + apply is_east_threatened_correct2; auto.
    + apply is_west_threatened_correct2; auto.
Qed.

Definition is_diag_threatened b pos pl :=
  exists pos',
    pos <> pos' /\ (
    lookup_piece pos' b = Some (pl, Bishop) \/
    lookup_piece pos' b = Some (pl, Queen)
  ) /\
  diag_adj b pos' pos.

Definition is_ne_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) northeast pos (wf_ne pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Bishop | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_se_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) southeast pos (wf_se pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Bishop | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_nw_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) northwest pos (wf_nw pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Bishop | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_sw_threatened
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  let o := (find_first
    (fun p => 
      match lookup_piece p b with
      | Some _ => neqb p pos
      | None => false
      end) southwest pos (wf_sw pos)) in
    match o with
    | Some pos' =>
      match lookup_piece pos' b with
      | Some (pl', pc) =>
        match pc with
        | Bishop | Queen => player_eqb pl pl'
        | _ => false
        end
      | None => false
      end
    | None => false
    end.

Definition is_diag_threatenedb
  (b : Board) (pos : Pos) (pl : Player) : bool :=
  is_ne_threatened b pos pl ||
  is_se_threatened b pos pl ||
  is_nw_threatened b pos pl ||
  is_sw_threatened b pos pl.

Lemma dist_translate_l x : forall y z,
  Dist.dist (x + y) (x + z) =
  Dist.dist y z.
Proof.
  induction x as [|x']; intros y z; simpl; auto.
Qed.

Lemma dist_translate_r x : forall y z,
  Dist.dist (y + x) (z + x) =
  Dist.dist y z.
Proof.
  intros y z.
  rewrite (PeanoNat.Nat.add_comm y).
  rewrite (PeanoNat.Nat.add_comm z).
  apply dist_translate_l.
Qed.

Lemma is_ne_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Bishop) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  diag_adj b pos' pos ->
  (val (fst pos) <= val (fst pos'))%nat ->
  (val (snd pos) <= val (snd pos'))%nat ->
  is_ne_threatened b pos pl = true.
Proof.
  intros Hneq look pf_d le1 le2.
  destruct (le_diff le1) as [dx Hdx].
  destruct (le_diff le2) as [dy Hdy].
  destruct pf_d as [diag no_betw].
  unfold diag_preadj in diag.
  assert (dx = dy).
  { unfold rank_dist, file_dist, rank, file,
      fin_dist in diag.
    rewrite <- Hdx, <- Hdy in diag.
    rewrite (Dist.dist_sym _ (val (snd pos))) in diag.
    rewrite (Dist.dist_sym _ (val (fst pos))) in diag.
    repeat rewrite dist_add in diag; auto.
  }
  subst.
  unfold is_ne_threatened.
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_ne_Some in Hn1.
    destruct Hn1 as [Hf Hr].
    assert (n = dy).
    { destruct (PeanoNat.Nat.lt_trichotomy n dy)
        as [nd|[nd|nd]]; auto.
      + apply find_first_pred in Hfind'.
        rewrite no_betw in Hfind'; [discriminate| | |].
        * unfold diag_preadj, rank, file,
            rank_dist, file_dist, fin_dist.
          rewrite <- Hdx, <- Hdy, Hf, Hr.
          repeat rewrite dist_translate_l; auto.
        * right; unfold file.
          rewrite <- Hdx, Hf; split; [|lia].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
        * right; unfold rank.
          rewrite <- Hdy, Hr; split; [|lia].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
      + apply Hn2 with (z := pos') in nd.
        * destruct look as [look|look];
          rewrite look in nd.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
        * rewrite iter_ne_Some; split; auto.
    }
    subst.
    assert (p = pos').
    { apply injective_projections.
      + apply val_inj.
        rewrite Hf; auto.
      + apply val_inj; lia.
    }
    subst.
    destruct look as [look|look]; rewrite look;
      apply player_eqb_refl.
  - apply find_first_None
      with (n := dy) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_ne_Some.
      split; auto.
Qed.

Lemma is_ne_threatened_correct2 b pos pl :
  is_ne_threatened b pos pl = true ->
  is_diag_threatened b pos pl.
Proof.
  intro pf.
  unfold is_ne_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    split.
    + rewrite iter_ne_Some in Hd1; destruct Hd1 as [df dr].
      unfold diag_preadj, rank_dist, file_dist, fin_dist,
        rank, file.
      rewrite df, dr.
      rewrite (Dist.dist_sym _ (val (snd pos))).
      rewrite (Dist.dist_sym _ (val (fst pos))).
      repeat rewrite dist_add; auto.
    + intros p' diag no_betw_f no_betw_r.
      rewrite iter_ne_Some in Hd1.
      destruct Hd1 as [df dr].
      destruct no_betw_f as [no_betw_f|no_betw_f].
      * unfold file in no_betw_f; lia.
      * destruct no_betw_r as [no_betw_r|no_betw_r].
        -- unfold rank in no_betw_r; lia.
        -- destruct no_betw_f as [no_betw_f1 no_betw_f2].
           destruct no_betw_r as [no_betw_r1 no_betw_r2].
           destruct (lt_diff no_betw_f1) as [dx Hdx].
           destruct (lt_diff no_betw_r1) as [dy Hdy].
           destruct (lt_diff no_betw_f2) as [dx' Hdx'].
           destruct (lt_diff no_betw_r2) as [dy' Hdy'].
           unfold diag_preadj in diag.
           unfold rank_dist, file_dist, rank, file,
             fin_dist in *.
           rewrite <- Hdx', <- Hdy' in diag.
           rewrite (Dist.dist_sym _ (val (fst p'))) in diag.
           rewrite (Dist.dist_sym _ (val (snd p'))) in diag.
           repeat rewrite dist_add in diag.
           assert (dx = dy) by lia; subst.
           assert (dy < d)%nat as dy_d by lia.
           symmetry in Hdx, Hdy.
           setoid_rewrite iter_ne_Some in Hd2.
           specialize (Hd2 _ p' dy_d (conj Hdx Hdy)).
           destruct (lookup_piece p' b); auto.
           unfold neqb in Hd2.
           destruct eq_dec; [|discriminate].
           subst; lia.
Qed.

Lemma is_se_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Bishop) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  diag_adj b pos' pos ->
  (val (fst pos) <= val (fst pos'))%nat ->
  (val (snd pos') <= val (snd pos))%nat ->
  is_se_threatened b pos pl = true.
Proof.
  intros Hneq look pf_d le1 le2.
  destruct (le_diff le1) as [dx Hdx].
  destruct (le_diff le2) as [dy Hdy].
  destruct pf_d as [diag no_betw].
  unfold diag_preadj in diag.
  assert (dx = dy).
  { unfold rank_dist, file_dist, rank, file,
      fin_dist in diag.
    rewrite <- Hdx, <- Hdy in diag.
    rewrite (Dist.dist_sym _ (val (fst pos))) in diag.
    repeat rewrite dist_add in diag; auto.
  }
  subst.
  unfold is_se_threatened.
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_se_Some in Hn1.
    destruct Hn1 as [Hf Hr].
    assert (n = dy).
    { destruct (PeanoNat.Nat.lt_trichotomy n dy)
        as [nd|[nd|nd]]; auto.
      + apply find_first_pred in Hfind'.
        rewrite no_betw in Hfind'; [discriminate| | |].
        * unfold diag_preadj, rank, file,
            rank_dist, file_dist, fin_dist.
          rewrite <- Hdx, Hf.
          rewrite <- (dist_translate_r dy) at 1.
          rewrite Hdy, <- Hr.
          repeat rewrite dist_translate_l.
          apply Dist.dist_sym.
        * right; unfold file.
          rewrite <- Hdx, Hf; split; [|lia].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
        * left; unfold rank; split; [lia|].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
      + apply Hn2 with (z := pos') in nd.
        * destruct look as [look|look];
          rewrite look in nd.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
        * rewrite iter_se_Some; split; auto.
    }
    subst.
    assert (p = pos').
    { apply injective_projections.
      + apply val_inj.
        rewrite Hf; auto.
      + apply val_inj; lia.
    }
    subst.
    destruct look as [look|look]; rewrite look;
      apply player_eqb_refl.
  - apply find_first_None
      with (n := dy) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_se_Some.
      split; auto.
Qed.

Lemma is_se_threatened_correct2 b pos pl :
  is_se_threatened b pos pl = true ->
  is_diag_threatened b pos pl.
Proof.
  intro pf.
  unfold is_se_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    split.
    + rewrite iter_se_Some in Hd1; destruct Hd1 as [df dr].
      unfold diag_preadj, rank_dist, file_dist, fin_dist,
        rank, file.
      rewrite df, <- dr.
      rewrite (Dist.dist_sym _ (val (fst pos))).
      repeat rewrite dist_add; auto.
    + intros p' diag no_betw_f no_betw_r.
      rewrite iter_se_Some in Hd1.
      destruct Hd1 as [df dr].
      destruct no_betw_f as [no_betw_f|no_betw_f].
      * unfold file in no_betw_f; lia.
      * destruct no_betw_r as [no_betw_r|no_betw_r].
        -- destruct no_betw_f as [no_betw_f1 no_betw_f2].
           destruct no_betw_r as [no_betw_r1 no_betw_r2].
           destruct (lt_diff no_betw_f1) as [dx Hdx].
           destruct (lt_diff no_betw_r1) as [dy Hdy].
           destruct (lt_diff no_betw_f2) as [dx' Hdx'].
           destruct (lt_diff no_betw_r2) as [dy' Hdy'].
           unfold diag_preadj in diag.
           unfold rank_dist, file_dist, rank, file,
             fin_dist in *.
           rewrite <- Hdx', <- Hdy in diag.
           rewrite (Dist.dist_sym _ (val (fst p'))) in diag.
           repeat rewrite dist_add in diag; subst.
           assert (dx = dy') by lia; subst.
           assert (dy' < d)%nat as dy'_d by lia.
           symmetry in Hdx, Hdy.
           setoid_rewrite iter_se_Some in Hd2.
           specialize (Hd2 _ p' dy'_d (conj Hdx Hdy')).
           destruct (lookup_piece p' b); auto.
           unfold neqb in Hd2.
           destruct eq_dec; [|discriminate].
           subst; lia.
        -- unfold rank in no_betw_r; lia.
Qed.

Lemma is_nw_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Bishop) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  diag_adj b pos' pos ->
  (val (fst pos') <= val (fst pos))%nat ->
  (val (snd pos) <= val (snd pos'))%nat ->
  is_nw_threatened b pos pl = true.
Proof.
  intros Hneq look pf_d le1 le2.
  destruct (le_diff le1) as [dx Hdx].
  destruct (le_diff le2) as [dy Hdy].
  destruct pf_d as [diag no_betw].
  unfold diag_preadj in diag.
  assert (dx = dy).
  { unfold rank_dist, file_dist, rank, file,
      fin_dist in diag.
    rewrite <- Hdx, <- Hdy in diag.
    rewrite (Dist.dist_sym _ (val (snd pos))) in diag.
    repeat rewrite dist_add in diag; auto.
  }
  subst.
  unfold is_nw_threatened.
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_nw_Some in Hn1.
    destruct Hn1 as [Hf Hr].
    assert (n = dy).
    { destruct (PeanoNat.Nat.lt_trichotomy n dy)
        as [nd|[nd|nd]]; auto.
      + apply find_first_pred in Hfind'.
        rewrite no_betw in Hfind'; [discriminate| | |].
        * unfold diag_preadj, rank, file,
            rank_dist, file_dist, fin_dist.
          rewrite <- Hdy, Hr.
          rewrite <- (dist_translate_r n (val (fst pos'))).
          rewrite Hf, <- Hdx.
          repeat rewrite dist_translate_l.
          apply Dist.dist_sym.
        * left; unfold file.
          rewrite <- Hf.
          split; [lia|].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
        * right; unfold rank; split; [|lia].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
      + apply Hn2 with (z := pos') in nd.
        * destruct look as [look|look];
          rewrite look in nd.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
        * rewrite iter_nw_Some; split; auto.
    }
    subst.
    assert (p = pos').
    { apply injective_projections; apply val_inj; lia.
    }
    subst.
    destruct look as [look|look]; rewrite look;
      apply player_eqb_refl.
  - apply find_first_None
      with (n := dy) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_nw_Some.
      split; auto.
Qed.

Lemma is_nw_threatened_correct2 b pos pl :
  is_nw_threatened b pos pl = true ->
  is_diag_threatened b pos pl.
Proof.
  intro pf.
  unfold is_nw_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    split.
    + rewrite iter_nw_Some in Hd1; destruct Hd1 as [df dr].
      unfold diag_preadj, rank_dist, file_dist, fin_dist,
        rank, file.
      rewrite <- df, dr.
      rewrite (Dist.dist_sym _ (val (snd pos))).
      repeat rewrite dist_add; auto.
    + intros p' diag no_betw_f no_betw_r.
      rewrite iter_nw_Some in Hd1.
      destruct Hd1 as [df dr].
      destruct no_betw_f as [no_betw_f|no_betw_f].
      * destruct no_betw_r as [no_betw_r|no_betw_r].
        -- unfold rank in no_betw_r; lia.
        -- destruct no_betw_f as [no_betw_f1 no_betw_f2].
           destruct no_betw_r as [no_betw_r1 no_betw_r2].
           destruct (lt_diff no_betw_f1) as [dx Hdx].
           destruct (lt_diff no_betw_r1) as [dy Hdy].
           destruct (lt_diff no_betw_f2) as [dx' Hdx'].
           destruct (lt_diff no_betw_r2) as [dy' Hdy'].
           unfold diag_preadj in diag.
           unfold rank_dist, file_dist, rank, file,
             fin_dist in *.
           rewrite <- Hdx, <- Hdy' in diag.
           rewrite (Dist.dist_sym _ (val (snd p')))
             in diag.
           repeat rewrite dist_add in diag; subst.
           assert (dx' = dy) by lia; subst.
           assert (dy < d)%nat as dy_d by lia.
           setoid_rewrite iter_nw_Some in Hd2.
           symmetry in Hdy.
           specialize (Hd2 _ p' dy_d (conj Hdx' Hdy)).
           destruct (lookup_piece p' b); auto.
           unfold neqb in Hd2.
           destruct eq_dec; [|discriminate].
           subst; lia.
      * unfold file in no_betw_f; lia.
Qed.

Lemma is_sw_threatened_correct1 b pl pos pos' :
  pos <> pos' ->
  (lookup_piece pos' b = Some (pl, Bishop) \/
  lookup_piece pos' b = Some (pl, Queen)) ->
  diag_adj b pos' pos ->
  (val (fst pos') <= val (fst pos))%nat ->
  (val (snd pos') <= val (snd pos))%nat ->
  is_sw_threatened b pos pl = true.
Proof.
  intros Hneq look pf_d le1 le2.
  destruct (le_diff le1) as [dx Hdx].
  destruct (le_diff le2) as [dy Hdy].
  destruct pf_d as [diag no_betw].
  unfold diag_preadj in diag.
  assert (dx = dy).
  { unfold rank_dist, file_dist, rank, file,
      fin_dist in diag.
    rewrite <- Hdx, <- Hdy in diag.
    repeat rewrite dist_add in diag; auto.
  }
  subst.
  unfold is_sw_threatened.
  destruct find_first eqn:Hfind.
  - pose proof (Hfind' := Hfind).
    apply find_first_is_first in Hfind.
    destruct Hfind as [n [Hn1 Hn2]].
    rewrite iter_sw_Some in Hn1.
    destruct Hn1 as [Hf Hr].
    assert (n = dy).
    { destruct (PeanoNat.Nat.lt_trichotomy n dy)
        as [nd|[nd|nd]]; auto.
      + apply find_first_pred in Hfind'.
        rewrite no_betw in Hfind'; [discriminate| | |].
        * unfold diag_preadj, rank, file,
            rank_dist, file_dist, fin_dist.
          rewrite <- (dist_translate_r n _ (val (snd p))).
          rewrite <- (dist_translate_r n _ (val (fst p))).
          rewrite Hf, Hr, <- Hdx, <- Hdy.
          repeat rewrite dist_translate_l; auto.
        * left; unfold file.
          split; [lia|].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
        * left; unfold rank.
          split; [lia|].
          destruct n; [|lia].
          assert (p = pos).
          { rewrite <- plus_n_O in Hf, Hr.
            apply val_inj in Hf, Hr.
            apply injective_projections; auto.
          }
          subst.
          destruct (lookup_piece pos b); [|discriminate].
          unfold neqb in Hfind'.
          destruct eq_dec;
            [discriminate|contradiction].
      + apply Hn2 with (z := pos') in nd.
        * destruct look as [look|look];
          rewrite look in nd.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
          -- unfold neqb in nd.
             destruct eq_dec; [|discriminate].
             subst; contradiction.
        * rewrite iter_sw_Some; split; auto.
    }
    subst.
    assert (p = pos').
    { apply injective_projections; apply val_inj; lia.
    }
    subst.
    destruct look as [look|look]; rewrite look;
      apply player_eqb_refl.
  - apply find_first_None
      with (n := dy) (y := pos') in Hfind.
    + destruct look as [look|look];
              rewrite look in Hfind.
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
      * elim Hneq; unfold neqb in Hfind.
        destruct eq_dec; [auto|discriminate].
    + rewrite iter_sw_Some.
      split; auto.
Qed.

Lemma is_sw_threatened_correct2 b pos pl :
  is_sw_threatened b pos pl = true ->
  is_diag_threatened b pos pl.
Proof.
  intro pf.
  unfold is_sw_threatened in pf.
  destruct find_first eqn:Hfind; [|discriminate].
  pose proof (Hfind' := Hfind).
  apply find_first_pred in Hfind.
  destruct (lookup_piece p b) as [[pl' pc']|] eqn:Hlook;
    [|discriminate].
  unfold neqb in Hfind.
  destruct eq_dec; [discriminate|].
  exists p; split; auto; split.
  - destruct pc'; try discriminate.
    + apply player_eqb_true in pf; subst; now right.
    + apply player_eqb_true in pf; subst.
      now left.
  - apply find_first_is_first in Hfind'.
    destruct Hfind' as [d [Hd1 Hd2]].
    split.
    + rewrite iter_sw_Some in Hd1; destruct Hd1 as [df dr].
      unfold diag_preadj, rank_dist, file_dist, fin_dist,
        rank, file.
      rewrite <- df, <- dr.
      repeat rewrite dist_add; auto.
    + intros p' diag no_betw_f no_betw_r.
      rewrite iter_sw_Some in Hd1.
      destruct Hd1 as [df dr].
      destruct no_betw_f as [no_betw_f|no_betw_f].
      * destruct no_betw_r as [no_betw_r|no_betw_r].
        -- destruct no_betw_f as [no_betw_f1 no_betw_f2].
           destruct no_betw_r as [no_betw_r1 no_betw_r2].
           destruct (lt_diff no_betw_f1) as [dx Hdx].
           destruct (lt_diff no_betw_r1) as [dy Hdy].
           destruct (lt_diff no_betw_f2) as [dx' Hdx'].
           destruct (lt_diff no_betw_r2) as [dy' Hdy'].
           unfold diag_preadj in diag.
           unfold rank_dist, file_dist, rank, file,
             fin_dist in *.
           rewrite <- Hdx, <- Hdy in diag.
           repeat rewrite dist_add in diag; subst.
           assert (dx' = dy') by lia; subst.
           assert (dy' < d)%nat as dy'_d by lia.
           setoid_rewrite iter_sw_Some in Hd2.
           specialize (Hd2 _ p' dy'_d (conj Hdx' Hdy')).
           destruct (lookup_piece p' b); auto.
           unfold neqb in Hd2.
           destruct eq_dec; [|discriminate].
           subst; lia.
        -- unfold rank in no_betw_r; lia.
      * unfold file in no_betw_f; lia.
Qed.

Lemma is_diag_threatened_iff b pos pl :
  is_diag_threatened b pos pl <->
  is_diag_threatenedb b pos pl = true.
Proof.
  split; intro pf.
  - destruct pf as [pos' [pf_neq [look diag]]].
    unfold is_diag_threatenedb.
    repeat rewrite orb_true_iff.
    destruct (PeanoNat.Nat.le_ge_cases
      (val (fst pos)) (val (fst pos')));
    destruct (PeanoNat.Nat.le_ge_cases
      (val (snd pos)) (val (snd pos'))).
    (* NE *)
    + left; left; left; apply is_ne_threatened_correct1
        with (pos' := pos'); auto.
    (* SE *)
    + left; left; right; apply is_se_threatened_correct1
        with (pos' := pos'); auto.
    (* NW *)
    + left; right; apply is_nw_threatened_correct1
        with (pos' := pos'); auto.
    (* SW *)
    + right; apply is_sw_threatened_correct1
        with (pos' := pos'); auto.
  - unfold is_diag_threatenedb in pf.
    repeat rewrite orb_true_iff in pf.
    destruct pf as [[[|]|]|].
    + now apply is_ne_threatened_correct2.
    + now apply is_se_threatened_correct2.
    + now apply is_nw_threatened_correct2.
    + now apply is_sw_threatened_correct2.
Qed.

Definition is_threatened_byb (b : Board) (pos : Pos) (pl : Player) : bool :=
     is_threatened_by_knight b pos pl
  || is_threatened_by_king b pos pl
  || is_orthog_threatenedb b pos pl
  || is_diag_threatenedb b pos pl.

Lemma is_threatened_byb_iff b pos pl :
  is_threatened_by b pos pl <->
  is_threatened_byb b pos pl = true.
Proof.
  unfold is_threatened_byb.
  repeat rewrite orb_true_iff.
  split.
  - intros [pc [pos' [pf_neq [pf1 pf2]]]].
    destruct pc.
    + do 2 left; right.
      rewrite <- is_threatened_by_king_iff.
      exists pos'; now split.
    + destruct pf2.
      * right.
        rewrite <- is_diag_threatened_iff.
        exists pos'; split; auto.
      * left; right.
        rewrite <- is_orthog_threatened_iff.
        exists pos'; split; auto.
    + left; right.
      rewrite <- is_orthog_threatened_iff.
      exists pos'; split; auto.
    + right.
      rewrite <- is_diag_threatened_iff.
      exists pos'; split; auto.
    + do 3 left.
      rewrite <- is_threatened_by_knight_iff.
      exists pos'; now split.
  - intros [[[knight|king]|orthog]|diag].
    + rewrite <- is_threatened_by_knight_iff in knight.
      destruct knight as [pos' pf].
      exists Knight, pos'; auto.
    + rewrite <- is_threatened_by_king_iff in king.
      destruct king as [pos' pf].
      exists King, pos'; auto.
    + rewrite <- is_orthog_threatened_iff in orthog.
      destruct orthog as
        [pos' [pf_neq [[pf1|pf1] pf2]]].
      * exists Rook, pos'. now split.
      * exists Queen, pos'; repeat split; auto.
        now right.
    + rewrite <- is_diag_threatened_iff in diag.
      destruct diag as [pos' [pf_neq [[pf1|pf1] pf2]]].
      * exists Bishop, pos'; split; auto.
      * exists Queen, pos'; repeat split; auto.
        now left.
Qed.

Lemma is_threatened_byb_false_iff b pos pl :
  ~ is_threatened_by b pos pl <->
  is_threatened_byb b pos pl = false.
Proof.
  rewrite is_threatened_byb_iff.
  split; intro; now destruct is_threatened_byb.
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
