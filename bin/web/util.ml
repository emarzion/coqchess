open Js_of_ocaml
open Compat

let create_element tag =
  Dom_html.document##createElement (Js.string tag)
let append_child parent child =
  Dom.appendChild parent child
let set_style el key value = ignore
  (el##.style##setProperty (Js.string key) (Js.string value) Js.undefined)
let log x = Firebug.console##log x
let log_player pl =
  log (string_of_player pl)