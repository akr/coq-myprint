open Names
open GlobRef
open Pp
open CErrors
open Goptions

let opt_showprop = ref true
let _ = declare_bool_option
        { optdepr  = false;
          optname  = "MyPrint ShowProp";
          optkey   = ["MyPrint";"ShowProp"];
          optread  = (fun () -> !opt_showprop);
          optwrite = (:=) opt_showprop }

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

let pr_sort sigma sort =
  let s = EConstr.ESorts.kind sigma sort in
  match s with
  | Sorts.SProp ->
      str "(Sort" ++ spc () ++ str "SProp)"
  | Sorts.Prop ->
      str "(Sort" ++ spc () ++ str "Prop)"
  | Sorts.Set ->
      str "(Sort" ++ spc () ++ str "Set)"
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
  str "ci_npar=" ++ int ci.Constr.ci_npar ++ spc () ++
  hv 2 (str "ci_cstr_ndecls=[" ++
    pp_join_ary (spc ()) (Array.map int ci.Constr.ci_cstr_ndecls) ++
  str "]") ++ spc () ++
  hv 2 (str "ci_cstr_nargs=[" ++
    pp_join_ary (spc ()) (Array.map int ci.Constr.ci_cstr_nargs) ++
  str "]") ++ str ")"

let push_rec_types env sigma (nameary,tyary,funary) =
  let to_constr = EConstr.to_constr sigma in
  Environ.push_rec_types (nameary, Array.map to_constr tyary, Array.map to_constr funary) env

let rec pp_term env sigma term =
  if !opt_showprop then
    hv 2 (pp_term_content env sigma term)
  else
    let ty = Retyping.get_type_of env sigma term in
    if Termops.is_Prop sigma ty then
      str "<prop>"
    else
      let ty2 = Retyping.get_type_of env sigma ty in
      if Termops.is_Prop sigma ty2 then
        str "<proof>"
      else
        hv 2 (
              (* str "<" ++ (Printer.pr_econstr_env env sigma ty) ++ str "><<" ++ (Printer.pr_econstr_env env sigma ty2) ++ str ">>" ++ *)
              pp_term_content env sigma term)
and pp_term_content env sigma term =
  match EConstr.kind sigma term with
  | Constr.Rel i -> str "(Rel" ++ spc () ++ int i ++ str ")"
  | Constr.Var name -> str "(Var" ++ spc () ++ str (Id.to_string name) ++ str ")"
  | Constr.Meta i -> str "(Meta" ++ spc () ++ int i ++ str ")"
  | Constr.Evar (ekey, termary) ->
      let pp = str "(Evar" ++ spc () ++ int (Evar.repr ekey) in
      List.fold_left
        (fun pp t -> pp ++ spc () ++ pp_term env sigma t)
        pp (Array.to_list termary) ++
      str ")"
  | Constr.Sort s -> pr_sort sigma s
  | Constr.Cast (expr, kind, ty) ->
      str "(Cast " ++
      (pp_term env sigma expr) ++ spc () ++
      str (match kind with
      | Constr.VMcast -> "VM"
      | Constr.NATIVEcast -> "NATIVE"
      | Constr.DEFAULTcast -> "DEFAULT"
      | Constr.REVERTcast -> "REVERT") ++ spc () ++
      (pp_term env sigma ty) ++ str ")"
  | Constr.Prod (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      let name = Context.binder_name name in
      str "(Prod" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term env sigma ty)) ++ spc () ++
      (pp_term env2 sigma body) ++ str ")"
  | Constr.Lambda (name, ty, body) ->
      let decl = Context.Rel.Declaration.LocalAssum (name, ty) in
      let env2 = EConstr.push_rel decl env in
      let name = Context.binder_name name in
      str "(Lambda" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term env sigma ty)) ++ spc () ++
      (pp_term env2 sigma body) ++ str ")"
  | Constr.LetIn (name, expr, ty, body) ->
      let decl = Context.Rel.Declaration.LocalDef (name, expr, ty) in
      let env2 = EConstr.push_rel decl env in
      let name = Context.binder_name name in
      str "(Let" ++ spc () ++
      hv 2 (
        str (string_of_name name) ++ spc () ++
        (pp_term env sigma ty)) ++ spc () ++
      (pp_term env sigma expr) ++ spc () ++
      (pp_term env2 sigma body) ++ str ")"
  | Constr.App (f, argsary) ->
      let pp = str "(App" ++ spc () ++ (pp_term env sigma f) in
      (List.fold_left
        (fun pp a -> pp ++ spc () ++ pp_term env sigma a)
        pp (Array.to_list argsary)) ++
      str ")"
  | Constr.Const cu ->
      let (c, _) = cu in (* strip EConstr.EInstance.t *)
      str "(Const" ++ spc () ++
      str (Constant.to_string c) ++
      str ")"
  | Constr.Ind iu ->
      let ((mutind, i), _) = iu in (* strip EConstr.EInstance.t *)
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let ind_id = oind_body.Declarations.mind_typename in
      str "(Ind" ++ spc () ++
      str (MutInd.to_string mutind) ++ spc () ++
      int i ++ spc () ++
      Id.print ind_id ++ str ")"
  | Constr.Construct cu ->
      let (((mutind, i), j), _) = cu in (* strip EConstr.EInstance.t *)
      let env = Global.env () in
      let mind_body = Environ.lookup_mind mutind env in
      let oind_body = mind_body.Declarations.mind_packets.(i) in
      let ind_id = oind_body.Declarations.mind_typename in
      let cons_id = oind_body.Declarations.mind_consnames.(j-1) in
      str "(Construct" ++ spc () ++
      str (MutInd.to_string mutind) ++ spc () ++
      int i ++ spc () ++
      int j ++ spc () ++
      Id.print ind_id ++ spc () ++
      Id.print cons_id ++ str ")"
  | Constr.Case (ci, tyf, expr, brs) ->
      let pp =
        str "(Case" ++ spc () ++
        hv 2 (pp_ci_info ci) ++ spc () ++
        (pp_term env sigma tyf) ++ spc () ++
        (pp_term env sigma expr)
      in
      (List.fold_left
        (fun pp br -> pp ++ spc () ++ pp_term env sigma br)
        pp (Array.to_list brs)) ++ str ")"
  | Constr.Fix arg ->
      let ((ia, i), (nameary, tyary, funary)) = arg in
      let env2 = push_rec_types env sigma (nameary, tyary, funary) in
      let pp = str "(Fix" ++ spc () ++ str (string_of_name (Context.binder_name (Array.get nameary i))) in
      List.fold_left
        (fun pp j ->
          let recidx = ia.(j) in
          let name = nameary.(j) in
          let ty = tyary.(j) in
          let f = funary.(j) in
          let name = Context.binder_name name in
          pp ++ spc () ++
          str "(" ++
          hv 2 (
            str (string_of_name name) ++ spc () ++
              str "decarg=" ++ int recidx ++ spc () ++
              (pp_term env sigma ty) ++ spc () ++
            (pp_term env2 sigma f) ++ str ")"))
        pp (iota_list 0 (Array.length funary)) ++
      str ")"
  | Constr.CoFix arg ->
      let (i, (nameary, tyary, funary)) = arg in
      let env2 = push_rec_types env sigma (nameary, tyary, funary) in
      let l2 = List.fold_right2
        (fun name ty l -> (name, ty) :: l)
        (Array.to_list nameary) (Array.to_list tyary) []
      in
      let l3 = List.fold_right2
        (fun (name, ty) f l -> (Context.binder_name name, ty, f) :: l)
        l2 (Array.to_list funary) []
      in
      let pp = str "(CoFix" ++ spc () ++ str (string_of_name (Context.binder_name (Array.get nameary i))) in
      List.fold_left
        (fun pp (name, ty, f) ->
          pp ++ spc () ++
          str "(" ++
          hv 2 (
            hv 0 (str (string_of_name name) ++ spc () ++
            (pp_term env sigma ty)) ++ spc () ++
          (pp_term env2 sigma f) ++ str ")"))
        pp l3 ++
      str ")"
  | Constr.Proj (proj, expr) ->
      str "(Proj" ++ spc () ++
      str (Projection.to_string proj) ++
      str "(" ++
      str "npars=" ++ int (Projection.npars proj) ++ str "," ++
      str "arg=" ++ int (Projection.arg proj) ++ str ")" ++ spc () ++
      (pp_term env sigma expr) ++ str ")"
  | Constr.Int n ->
      str "(Int" ++ spc () ++
      str (Uint63.to_string n) ++ str ")"
  | Constr.Float n ->
      str "(Float" ++ spc () ++
      str (Float64.to_string n) ++ str ")"

let pp_name name =
  match name with
  | Names.Name.Anonymous -> str "_"
  | Names.Name.Name id -> str (Id.to_string id)

let pp_context_rel_decl env sigma decl =
  match decl with
  | Context.Rel.Declaration.LocalAssum (name, ty) ->
      let name = Context.binder_name name in
      str "(" ++ pp_name name ++ str ":" ++ Printer.pr_constr_env env sigma ty ++ str ")"
  | Context.Rel.Declaration.LocalDef (name, expr, ty) ->
      let name = Context.binder_name name in
      str "(" ++ pp_name name ++ str ":" ++
      Printer.pr_constr_env env sigma ty ++ str ":=" ++
      Printer.pr_constr_env env sigma expr ++ str ")"

let type_of_inductive_arity mind_arity : Constr.t =
  match mind_arity with
  | Declarations.RegularArity regind_arity -> regind_arity.Declarations.mind_user_arity
  | Declarations.TemplateArity temp_arity -> Constr.mkType (temp_arity : Declarations.template_arity).Declarations.template_level

let pp_ind env sigma ind =
  let (mutind, i) = ind in
  let mutind_body = Environ.lookup_mind mutind env in
  let env = Environ.push_rel_context (
    List.map (fun oneind_body ->
      Context.Rel.Declaration.LocalAssum (Context.annotR (Names.Name.Name oneind_body.Declarations.mind_typename), type_of_inductive_arity oneind_body.Declarations.mind_arity))
      (List.rev (Array.to_list mutind_body.Declarations.mind_packets))
  ) env in
  hv 2 (str "(MutInd" ++ spc () ++
    str (Id.to_string mutind_body.Declarations.mind_packets.(i).Declarations.mind_typename) ++
    spc () ++ str "mind_record=" ++ str (match mutind_body.Declarations.mind_record with Declarations.NotRecord -> "NotRecord" | Declarations.FakeRecord -> "FakeRecord" | Declarations.PrimRecord _ -> "PrimRecord") ++
    spc () ++ str "mind_finite=" ++ str (match mutind_body.Declarations.mind_finite with Declarations.Finite -> "Finite" | Declarations.CoFinite -> "CoFinite" | Declarations.BiFinite -> "BiFinite") ++
    spc () ++ str "mind_ntypes=" ++ int mutind_body.Declarations.mind_ntypes ++
    spc () ++ str "mind_nparams=" ++ int mutind_body.Declarations.mind_nparams ++
    spc () ++ str "mind_nparams_rec=" ++ int mutind_body.Declarations.mind_nparams_rec ++
    spc () ++ hv 2 (str "mind_params_ctxt=[" ++
      pp_join_list (spc ())
        (List.map
          (pp_context_rel_decl env sigma)
          mutind_body.Declarations.mind_params_ctxt) ++ str "]") ++
    pp_prejoin_ary (spc ())
      (Array.map
        (fun oneind_body ->
          hv 2 (str "(" ++
          str (Id.to_string oneind_body.Declarations.mind_typename) ++
          spc () ++ hv 2 (str "mind_arity_ctxt=[" ++ pp_join_list (spc ())
              (List.map
                (pp_context_rel_decl env sigma)
                oneind_body.Declarations.mind_arity_ctxt) ++ str "]") ++
          spc () ++ hv 2 (str "mind_user_lc=[" ++
            pp_join_ary (spc ())
              (Array.map2
                (fun consname user_lc ->
                  hv 2 (str "(" ++
                  str (Id.to_string consname) ++ spc () ++
                  Printer.pr_constr_env env sigma user_lc ++
                  str ")")
                )
                oneind_body.Declarations.mind_consnames
                oneind_body.Declarations.mind_user_lc) ++ str "]") ++
          spc () ++ hv 2 (str "mind_nf_lc=[" ++
            pp_join_ary (spc ())
              (Array.map2
                (fun consname nf_lc ->
                  let ((ctx : Constr.rel_context), (t : Constr.t)) = nf_lc in
                  let t = Context.Rel.fold_inside
                            (fun (t : Constr.t) (decl : Constr.rel_declaration) ->
                              match decl with
                              | Context.Rel.Declaration.LocalAssum (name, ty) -> Constr.mkProd (name, ty, t)
                              | Context.Rel.Declaration.LocalDef (name, expr, ty) -> Constr.mkLetIn (name, expr, ty, t))
                            ~init:t ctx in
                  hv 2 (str "(" ++
                  str (Id.to_string consname) ++ spc () ++
                  Printer.pr_constr_env env sigma t ++
                  str ")")
                )
                oneind_body.Declarations.mind_consnames
                oneind_body.Declarations.mind_nf_lc) ++ str "]") ++
          spc () ++ str "mind_nrealargs=" ++ int oneind_body.Declarations.mind_nrealargs ++
          spc () ++ str "mind_nrealdecls=" ++ int oneind_body.Declarations.mind_nrealdecls ++
          spc () ++ str "mind_consnrealargs=[" ++ hv 2 (pp_join_ary (spc ()) (Array.map int oneind_body.Declarations.mind_consnrealargs)) ++ str "]" ++
          spc () ++ str "mind_consnrealdecls=[" ++ hv 2 (pp_join_ary (spc ()) (Array.map int oneind_body.Declarations.mind_consnrealdecls)) ++ str "]" ++
          str ")")
        )
        mutind_body.Declarations.mind_packets) ++
    str ")")

let obtain_env_sigma (pstate : Proof_global.t option) =
  match pstate with
  | Some pstate -> let (sigma, env) = Pfedit.get_current_context pstate in (env, sigma)
  | None -> let env = Global.env () in (env, Evd.from_env env)

let print_term (pstate : Proof_global.t option) (term : Constrexpr.constr_expr) =
  let ((env : Environ.env), (sigma : Evd.evar_map)) = obtain_env_sigma pstate in
  let (sigma, (term3 : EConstr.constr)) = Constrintern.interp_constr_evars env sigma term in
  Feedback.msg_info (pp_term env sigma term3)

let print_type (pstate : Proof_global.t option) (term : Constrexpr.constr_expr) =
  let ((env : Environ.env), (sigma : Evd.evar_map)) = obtain_env_sigma pstate in
  let (sigma, (term3 : EConstr.constr)) = Constrintern.interp_constr_evars env sigma term in
  let ty = Retyping.get_type_of env sigma term3 in
  Feedback.msg_info (pp_term env sigma ty)

let print_term_type_n (pstate : Proof_global.t option) (n : int) (expr : Constrexpr.constr_expr) =
  let ((env : Environ.env), (sigma : Evd.evar_map)) = obtain_env_sigma pstate in
  let (sigma, (term2 : EConstr.constr)) = Constrintern.interp_constr_evars env sigma expr in
  Feedback.msg_info (pp_term env sigma term2);
  let termref = ref term2 in
  for _ = 1 to n do
    termref := Retyping.get_type_of env sigma !termref;
    Feedback.msg_info (pp_term env sigma !termref)
  done

let print_term_type (pstate : Proof_global.t option) (term : Constrexpr.constr_expr) =
  print_term_type_n pstate 1 term

let print_global (pstate : Proof_global.t option) (name : Libnames.qualid) =
  let ((env : Environ.env), (sigma : Evd.evar_map)) = obtain_env_sigma pstate in
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef c ->
     begin match Global.body_of_constant Library.indirect_accessor c with
     | Some (b, _, _) -> Feedback.msg_info (pp_term env sigma (EConstr.of_constr b))
     | None -> user_err (str "can't print axiom")
     end
  | VarRef _ -> user_err (str "can't print VarRef")
  | IndRef ind -> Feedback.msg_info (pp_ind env sigma ind)
  | ConstructRef _ -> user_err (str "can't print ConstructRef")

let rec pp_constr_expr (c : Constrexpr.constr_expr) =
  match CAst.with_val (fun x -> x) c with
  | Constrexpr.CRef (qid,iexpr_opt) ->
      str "(CRef" ++ spc () ++
      Ppconstr.pr_qualid qid ++
      str ")"
  | Constrexpr.CFix _ -> str "(CFix)"
  | Constrexpr.CCoFix _ -> str "(CCoFix)"
  | Constrexpr.CProdN _ -> str "(CProdN)"
  | Constrexpr.CLambdaN _ -> str "(CLambdaN)"
  | Constrexpr.CLetIn _ -> str "(CLetIn)"
  | Constrexpr.CAppExpl ((projflag, qid, iexpr_opt), args) ->
      str "(CAppExpl" ++
      (match projflag with | None -> mt () | Some i -> spc () ++ str "projflag=" ++ int i) ++
      spc () ++
      Ppconstr.pr_qualid qid ++
      pp_prejoin_list (spc ())
        (List.map (fun arg -> pp_constr_expr arg) args) ++
      str ")"
  | Constrexpr.CApp ((projflag, f), args) ->
      str "(CApp" ++
      (match projflag with | None -> mt () | Some i -> spc () ++ str "projflag=" ++ int i) ++
      spc () ++
      pp_constr_expr f ++
      pp_prejoin_list (spc ())
        (List.map (fun (arg, ex_opt) ->
          match ex_opt with
          | None -> pp_constr_expr arg
          | Some ex ->
              match CAst.with_val (fun x -> x) ex with
              | Constrexpr.ExplByPos _ -> str "ExplByPos" (* not implemented *)
              | Constrexpr.ExplByName id -> Id.print id ++ str ":=" ++ pp_constr_expr arg)
        args) ++
      str ")"
  | Constrexpr.CRecord _ -> str "(CRecord)"
  | Constrexpr.CCases _ -> str "(CCases)"
  | Constrexpr.CLetTuple _ -> str "(CLetTuple)"
  | Constrexpr.CIf _ -> str "(CIf)"
  | Constrexpr.CHole _ -> str "(CHole)"
  | Constrexpr.CPatVar _ -> str "(CPatVar)"
  | Constrexpr.CEvar _ -> str "(CEvar)"
  | Constrexpr.CSort _ -> str "(CSort)"
  | Constrexpr.CCast _ -> str "(CCast)"
  | Constrexpr.CNotation _ -> str "(CNotation)"
  | Constrexpr.CGeneralization _ -> str "(CGeneralization)"
  | Constrexpr.CPrim _ -> str "(CPrim)"
  | Constrexpr.CDelimiters _ -> str "(CDelimiters)"

let print_constr_expr (pstate : Proof_global.t option) (term : Constrexpr.constr_expr) =
  Feedback.msg_info (pp_constr_expr term)

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

let detect_recursive_functions (ctnt_i : Constant.t) : (int * Constant.t option array) option =
  let env = Global.env () in
  let sigma = Evd.from_env env in
  let modpath = KerName.modpath (Constant.canonical ctnt_i) in
  match Global.body_of_constant Library.indirect_accessor ctnt_i with
  | None -> user_err (Pp.str "couldn't obtain the definition of" ++ Pp.spc () ++
                      Printer.pr_constant env ctnt_i)
  | Some (def_i,_,_) ->
      let def_i = EConstr.of_constr def_i in
      let (ctx_rel_i, body_i) = EConstr.decompose_lam_assum sigma def_i in
      match EConstr.kind sigma body_i with
      | Constr.Fix ((ia, i), (nary, tary, fary)) ->
          let ctnt_ary =
            Array.mapi (fun j nm ->
              if j = i then
                Some ctnt_i
              else
                let nm = Context.binder_name nm in
                match nm with
                | Name.Anonymous -> None
                | Name.Name id ->
                    let label = Label.of_id id in
                    let ctnt_j = Constant.make1 (KerName.make modpath label) in
                    try
                      match Global.body_of_constant Library.indirect_accessor ctnt_j with
                      | None -> None
                      | Some (def_j,_,_) ->
                          let def_j = EConstr.of_constr def_j in
                          let body_j' = EConstr.mkFix ((ia, j), (nary, tary, fary)) in
                          let def_j' = EConstr.it_mkLambda_or_LetIn body_j' ctx_rel_i in
                          if EConstr.eq_constr sigma def_j def_j' then
                            Some ctnt_j
                          else
                            None
                    with Not_found -> None)
            nary
          in
          Some (i, ctnt_ary)
      | _ -> None

let print_rec (pstate : Proof_global.t option) (name : Libnames.qualid) =
  let ((env : Environ.env), (sigma : Evd.evar_map)) = obtain_env_sigma pstate in
  let reference = Smartlocate.global_with_alias name in
  match reference with
  | ConstRef c ->
      (match detect_recursive_functions c with
      | None -> Feedback.msg_info (Pp.str "No recursive function detected")
      | Some (i, ctnt_ary) ->
          Feedback.msg_info
            (Pp.str "Found recursive function: index=" ++ Pp.int i);
          Array.iteri (fun j ctnt_j_opt ->
            match ctnt_j_opt with
            | None -> Feedback.msg_info
                (Pp.str "Mutually recursive function" ++ Pp.spc () ++
                 Pp.str "(" ++ Pp.int j ++ Pp.str ") not found")
            | Some ctnt_j ->
                      Feedback.msg_info
                (Pp.str "Mutually recursive function" ++ Pp.spc () ++
                 Pp.str"(" ++ Pp.int j ++ Pp.str ") found:" ++ Pp.spc () ++
                 Printer.pr_constant env ctnt_j))
            ctnt_ary)
  | VarRef _ -> user_err (str "can't print VarRef")
  | IndRef ind -> Feedback.msg_info (pp_ind env sigma ind)
  | ConstructRef _ -> user_err (str "can't print ConstructRef")
