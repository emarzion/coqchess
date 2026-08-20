open Query.Read_file
open Model
open Ui

let () =
  let tb = make_tb in
  let state = ref Model.init in
  init tb state

(*
python3 -m http.server 8000
*)
