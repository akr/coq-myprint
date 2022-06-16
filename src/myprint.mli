open Names

val print_term : Declare.Proof.t option -> Constrexpr.constr_expr -> unit
val print_type : Declare.Proof.t option -> Constrexpr.constr_expr -> unit
val print_term_type : Declare.Proof.t option -> Constrexpr.constr_expr -> unit
val print_term_type_n : Declare.Proof.t option -> int -> Constrexpr.constr_expr -> unit
val print_global : Declare.Proof.t option -> Libnames.qualid -> unit
val print_constr_expr : Declare.Proof.t option -> Constrexpr.constr_expr -> unit
val print_rec : Declare.Proof.t option -> Libnames.qualid -> unit
val print_escape : Id.t -> unit
val print_goal : unit -> unit Proofview.tactic
