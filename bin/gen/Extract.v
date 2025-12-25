Require Import Extraction.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlNativeString.
Require Import ExtrOCamlInt63.
Extraction Language OCaml.

Require Import TBGen.Util.OMap.
Require Import Chess.TB.TB.

Set Warnings "-extraction-default-directory".

Extraction "TBGen.ml" certified_Chess_TB.
