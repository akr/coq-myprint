open Names
open Globnames
open Pp
open CErrors
open Goptions

let string_of_name name =
  match name with
  | Name.Name id -> Id.to_string id
  | Name.Anonymous -> "_"

let iota_ary m n =
  Array.init n (fun i -> m + i)

let iota_list m n =
  Array.to_list (iota_ary m n)

let pp_join_ary sep ary =
  if Array.length ary = 0 then
    mt ()
  else
    Array.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      ary.(0)
      (Array.sub ary 1 (Array.length ary - 1))

let pp_join_list sep l =
  match l with
  | [] ->
    mt ()
  | elt :: rest ->
    List.fold_left
      (fun pp elt -> pp ++ sep ++ elt)
      elt
      rest

let pp_prejoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (mt ())
    ary

let pp_prejoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ sep ++ elt)
    (mt ())
    l

let pp_postjoin_ary sep ary =
  Array.fold_left
    (fun pp elt -> if ismt elt then pp else pp ++ elt ++ sep)
    (mt ())
    ary

let pp_postjoin_list sep l =
  List.fold_left
    (fun pp elt -> pp ++ elt ++ sep)
    (mt ())
    l

let pr_sort sort =
  match sort with
  | Sorts.Prop p ->
      (if sort = Term.prop_sort then
        str "(Sort" ++ spc () ++ str "Prop)"
      else if sort = Term.set_sort then
        str "(Sort" ++ spc () ++ str "Set)"
      else
      (* not reached? *)
      str "(Sort" ++ spc () ++
      str (match p with
      | Sorts.Pos -> "Pos"
      | Sorts.Null ->"Null") ++
      str ")")
  | Sorts.Type u ->
      str "(Sort" ++ spc () ++
      str "Type" ++ spc () ++
      Univ.Universe.pr u ++ str ")"

let pp_ci_info ci =
  let (mutind, i) = ci.Constr.ci_ind in
  hv 2 (str "(" ++
    str "(Ind" ++ spc () ++
    str (MutInd.to_string mutind) ++ spc () ++
    int i ++ str ")") ++ spc () ++
  int ci.Constr.ci_npar ++ spc () ++
  hv 2 (str "[" ++
    pp_join_ary (spc ()) (Array.map int ci.Constr.ci_cstr_ndecls) ++
  str "]") ++ spc () ++
  hv 2 (str "[" ++
    pp_join_ary (spc ()) (Array.map int ci.Constr.ci_cstr_nargs) ++
  str "]") ++ str ")"

let rec pp_term term =
  hv 2 (pp_term_content term)
and pp_term_content term =
  match Term.kind_of_term term with
  | Term.Rel i -> str "(Rel" ++ spc () ++ int i ++ str ")"
  | Term.Var name -> str "(Var" ++ spc () ++ str (Id.to_string name) ++ str ")"
  | Term.Meta i -> str "(Meta" ++ spc () ++ int i ++ str ")"
  | Term.Evar (ekey, termary) ->
      let pp = str "(Evar" ++ spc () ++ int (Evar.repr ekey) in
      List.fold_left
        (fun pp t -> pp ++ spc () ++ pp_term t)
        pp (Array.to_list termary) ++
      str ")"
  | Term.Sort s -> pr_sort s
  | Term.Cast (expr, kind, ty) ->
      str "(Cast " ++
      (pp_term expr) ++ spc () ++
      str (match kind with
      | Constr.VMcast -> "VM"
      | Constr.NATIVEcast -> "NATIVE"
      | Constr.DEFAULTcast -> "DEFAULT"
      | Constr.REVERTcast -> "REVERT") ++ spc () ++
      (pp_term ty) ++ str ")"
  | Term.Prod (name, ty, body) ->
      str "(Prod" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term ty)) ++ spc () ++
      (pp_term body) ++ str ")"
  | Term.Lambda (name, ty, body) ->
      str "(Lambda" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term ty)) ++ spc () ++
      (pp_term body) ++ str ")"
  | Term.LetIn (name, expr, ty, body) ->
      str "(Let" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term ty)) ++ spc () ++
      (pp_term expr) ++ spc () ++
      (pp_term body) ++ str ")"
  | Term.App (f, argsary) ->
      let pp = str "(App" ++ spc () ++ (pp_term f) in
      (List.fold_left
        (fun pp a -> pp ++ spc () ++ pp_term a)
        pp (Array.to_list argsary)) ++
      str ")"
  | Term.Const cu ->
      let c = Univ.out_punivs cu in
      str "(Const" ++ spc () ++
      str (Constant.to_string c) ++
      str ")"
  | Term.Ind iu ->
      let (mutind, i) = Univ.out_punivs iu in
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.mind_packets.(i) in
      let ind_id = oind_body.mind_typename in
      str "(Ind" ++ spc () ++
      str (MutInd.to_string mutind) ++ spc () ++
      int i ++ spc () ++
      Id.print ind_id ++ str ")"
  | Term.Construct cu ->
      let ((mutind, i), j) = Univ.out_punivs cu in
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.mind_packets.(i) in
      let ind_id = oind_body.mind_typename in
      let cons_id = oind_body.mind_consnames.(j-1) in
      str "(Construct" ++ spc () ++
      str (MutInd.to_string mutind) ++ spc () ++
      int i ++ spc () ++
      int j ++ spc () ++
      Id.print ind_id ++ spc () ++
      Id.print cons_id ++ str ")"
  | Term.Case (ci, tyf, expr, brs) ->
      let pp =
        str "(Case" ++ spc () ++
        hv 2 (pp_ci_info ci) ++ spc () ++
        (pp_term tyf) ++ spc () ++
        (pp_term expr)
      in
      (List.fold_left
        (fun pp br -> pp ++ spc () ++ pp_term br)
        pp (Array.to_list brs)) ++ str ")"
  | Term.Fix arg ->
      let ((ia, i), (nameary, tyary, funary)) = arg in
      let pp = str "(Fix" ++ spc () ++ str (string_of_name (Array.get nameary i)) in
      List.fold_left
        (fun pp j ->
          let recidx = ia.(j) in
          let name = nameary.(j) in
          let ty = tyary.(j) in
          let f = funary.(j) in
          pp ++ spc () ++
          str "(" ++
          hv 2 (
            str (string_of_name name) ++ spc () ++
              str "[" ++ int recidx ++ str "]" ++ spc () ++
              (pp_term ty) ++ spc () ++
            (pp_term f) ++ str ")"))
        pp (iota_list 0 (Array.length funary)) ++
      str ")"
  | Term.CoFix arg ->
      let (i, (nameary, tyary, funary)) = arg in
      let l2 = List.fold_right2
        (fun name ty l -> (name, ty) :: l)
        (Array.to_list nameary) (Array.to_list tyary) []
      in
      let l3 = List.fold_right2
        (fun (name, ty) f l -> (name, ty, f) :: l)
        l2 (Array.to_list funary) []
      in
      let pp = str "(CoFix" ++ spc () ++ int i in
      List.fold_left
        (fun pp (name, ty, f) ->
          pp ++ spc () ++
          hv 2 (
            hv 0 (str (string_of_name name) ++ spc () ++
            (pp_term ty)) ++ spc () ++
          (pp_term f) ++ str ")"))
        pp l3 ++
      str ")"
  | Term.Proj (proj, expr) ->
      str "(Proj" ++ spc () ++
      str (Projection.to_string proj) ++ spc () ++
      (pp_term expr) ++ str ")"

let pp_name name =
  match name with
  | Names.Name.Anonymous -> str "_"
  | Names.Name.Name id -> str (Id.to_string id)

let pp_context_rel_decl decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) -> str "(" ++ pp_name name ++ str ":" ++ Printer.pr_constr ty ++ str ")"
  | Context.Rel.Declaration.LocalDef (name, expr, ty) -> str "localdef"

let type_of_inductive_arity mind_arity : Term.constr =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Term.mkSort (Sorts.Type (temp_arity : Declarations.template_arity).Declarations.template_level)

let pp_ind ind =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let env = Environ.push_rel_context (
    List.map (fun oneind_body ->
      Context.Rel.Declaration.LocalAssum (Names.Name.Name oneind_body.Declarations.mind_typename, type_of_inductive_arity oneind_body.Declarations.mind_arity))
      (List.rev (Array.to_list mutind_body.Declarations.mind_packets))
  ) env in
  hv 2 (str "(MutInd" ++ spc () ++
    str (Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename) ++
    pp_prejoin_list (spc ())
      (List.map
        pp_context_rel_decl
        mutind_body.Declarations.mind_params_ctxt) ++
    pp_prejoin_ary (spc ())
      (Array.map
        (fun oneind_body ->
          hv 2 (str "(" ++
          str (Id.to_string oneind_body.Declarations.mind_typename) ++
          pp_prejoin_list (spc ())
            (List.map
              pp_context_rel_decl
              oneind_body.Declarations.mind_arity_ctxt) ++
          pp_prejoin_ary (spc ())
            (Array.map2
              (fun consname user_lc ->
                hv 2 (str "(" ++
                str (Id.to_string consname) ++ spc () ++
                Printer.pr_constr_env env evd user_lc ++
                str ")")
              )
              oneind_body.Declarations.mind_consnames
              oneind_body.Declarations.mind_user_lc) ++
          str ")")
        )
        mutind_body.Declarations.mind_packets) ++
    str ")")

let print_term (term : Constrexpr.constr_expr) =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let ((term2 : Term.constr), (_ : Evd.evar_universe_context)) = Constrintern.interp_constr env evd term in
  Feedback.msg_info (pp_term term2)

let print_type (term : Constrexpr.constr_expr) =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let evdref = ref evd in
  let ((term2 : Term.constr), (_ : Evd.evar_universe_context)) = Constrintern.interp_constr env evd term in
  let ty = Typing.e_type_of env evdref term2 in
  Feedback.msg_info (pp_term ty)

let print_term_type_n (n : int) (expr : Constrexpr.constr_expr) =
  let ((evd : Evd.evar_map), (env : Environ.env)) = Lemmas.get_current_context () in
  let evdref = ref evd in
  let ((term : Term.constr), (_ : Evd.evar_universe_context)) = Constrintern.interp_constr env evd expr in
  Feedback.msg_info (pp_term term);
  let termref = ref term in
  for i = 1 to n do
    termref := Typing.e_type_of env evdref !termref;
    Feedback.msg_info (pp_term !termref)
  done

let print_term_type (term : Constrexpr.constr_expr) =
  print_term_type_n 1 term

let print_global (name : Libnames.reference) =
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef c ->
     begin match Global.body_of_constant c with
     | Some b -> Feedback.msg_info (pp_term b)
     | None -> error "can't print axiom"
     end
  | VarRef _ -> error "can't print VarRef"
  | IndRef ind -> Feedback.msg_info (pp_ind ind)
  | ConstructRef _ -> error "can't print ConstructRef"

let xhh_escape_string s =
  let len = String.length s in
  let buf = Buffer.create len in
  String.iter (fun ch ->
    let code = Char.code ch in
    if 0x20 <= code && code <= 0x7e then
      Buffer.add_char buf ch
    else
      Buffer.add_string buf (Printf.sprintf "\\x%02X" code))
    s;
  Buffer.contents buf

let print_escape (id : Id.t) =
  let s = Id.to_string id in
  Feedback.msg_info (str (xhh_escape_string s))
