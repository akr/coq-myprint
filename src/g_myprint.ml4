let () = Mltop.add_known_plugin (fun () ->
  Feedback.msg_info Pp.(str"myprint 0.1"))
  "myprint"

DECLARE PLUGIN "myprint_plugin"

open Myprint

open Constrarg (* for ident(...) *)
open Extraargs (* for lconstr(...). lconstr accepts "PrintTerm 1 + 1" addition to "PrintTerm (1 + 1)" *)
open Stdarg (* for wit_int *)

VERNAC COMMAND EXTEND Myprint CLASSIFIED AS QUERY
    | [ "PrintTerm" lconstr(term) ] -> [ print_term term ]
    | [ "PrintType" lconstr(term) ] -> [ print_type term ]
    | [ "PrintTermType" lconstr(term) ] -> [ print_term_type term ]
    | [ "PrintTermTypeN" int(n) lconstr(term) ] -> [ print_term_type_n n term ]
    | [ "PrintGlobal" global(name) ] -> [ print_global name ]
    | [ "PrintEscape" ident(id) ] -> [ print_escape id ]
END;;

