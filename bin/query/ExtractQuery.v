Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Require Import ExtrOCamlInt63.
Require Import Games.Util.Dec.
Require Import Chess.Util.Fin.
Extraction Language OCaml.

Require Import Chess.TB.MakeState.
Require Import Chess.Chess.Chess.
Require Import TBGen.StratSymTB.TB.
Require Import TBGen.StratSymTB.OCamlTB.

Set Warnings "-extraction-default-directory".

Definition query : OCamlTablebase ChessGame ->
  ChessState -> option (Player.Player * nat) :=
  query_TB.

Extraction "ExtractQuery.ml"
  mk_KRvK_bound
  exec_ChessMove
  query
  enum_chess_moves
  OCamlTablebase
  file_a file_b file_c file_d file_e file_f file_g file_h
  rank_1 rank_2 rank_3 rank_4 rank_5 rank_6 rank_7 rank_8.
