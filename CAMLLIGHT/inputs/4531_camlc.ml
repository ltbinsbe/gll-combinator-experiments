(* Printing of error messages and warnings *)

#open "misc";;
#open "location";;
#open "const";;
#open "globals";;
#open "syntax";;
#open "types";;
#open "pr_type";;
#open "interntl";;

let output_globalref oc = function
    GRname s ->
      output_string oc s
  | GRmodname q ->
      output_string oc q.qual; output_string oc "__"; output_string oc q.id
;;

(* Summary of output functions:
      %a location               output_location
      %t unit                   output_input_name
      %a type_desc global       output_type_constr
      %a value_desc global      output_value
      %a constr_desc global     output_constr
      %a label_desc global      output_label
      %a typ                    output_type, output_one_type, output_schema
      %a global_reference       output_globalref *)

(* The error messages themselves *)

let unbound_value_err name loc =
  eprintf "%aThe value identifier %a is unbound.\n" 
    output_location loc output_globalref name;
  raise Toplevel
and unbound_constr_err name loc =
  eprintf "%aThe constructor %a is unbound.\n"
    output_location loc output_globalref name;
  raise Toplevel
and unbound_label_err name loc =
  eprintf "%aThe label %a is unbound.\n"
    output_location loc output_globalref name;
  raise Toplevel
and unbound_type_constr_err name loc =
  eprintf "%aThe type constructor %a is unbound.\n"
    output_location loc output_globalref name;
  raise Toplevel
and unbound_type_var_err v ty =
  eprintf "%aThe type variable %s is unbound.\n"
    output_location ty.te_loc v;
  raise Toplevel
;;

let type_arity_err cstr args loc =
  eprintf "%aThe type constructor %a expects %d argument(s),\n\
           but is here given %d argument(s).\n"
    output_location loc
    output_type_constr cstr
    cstr.info.ty_arity
    (list_length args);
  raise Toplevel
;;

let non_linear_pattern_err pat name =
  eprintf "%aThe variable %s is bound several times in this pattern.\n"
    output_location pat.p_loc name;
  raise Toplevel
;;

let upper_case_variable_warning pat name =
  eprintf "%aWarning: the variable %s starts with an upper case letter in this pattern.\n"
    output_location pat.p_loc name;
  flush stderr
;;

let orpat_should_be_closed_err pat =
  eprintf "%aA pattern with \"|\" must not bind variables.\n"
    output_location pat.p_loc;
  raise Toplevel
;;

let pat_wrong_type_err pat actual_ty expected_ty =
  eprintf "%aThis pattern matches values of type %a,\n\
           but should match values of type %a.\n"
    output_location pat.p_loc
    output_one_type actual_ty
    output_type expected_ty;
  raise Toplevel
;;

let expr_wrong_type_err exp actual_ty expected_ty =
  eprintf "%aThis expression has type %a,\n\
           but is used with type %a.\n"
    output_location exp.e_loc
    output_one_type actual_ty
    output_type expected_ty;
  raise Toplevel
;;

let not_unit_type_warning exp actual_ty =
  eprintf "%aWarning: this expression has type %a,\n\
           but is used with type unit.\n"
    output_location exp.e_loc
    output_one_type actual_ty;
  flush stderr
;;

let application_of_non_function_err exp ty =
  begin try
    let _ = filter_arrow ty in
    eprintf "%aThis function is applied to too many arguments.\n"
      output_location exp.e_loc
  with Unify ->
    eprintf "%aThis expression is not a function, it cannot be applied.\n"
      output_location exp.e_loc
  end;
  raise Toplevel
;;

let ill_shaped_match_err exp =
  eprintf "%aThis curried matching contains cases of different lengths.\n"
    output_location exp.e_loc;
  raise Toplevel
;;

let duplicate_param_in_type_decl_err loc =
  eprintf "%aRepeated type parameter in type declaration.\n"
    output_location loc;
  raise Toplevel
;;

let not_mutable_err id loc =
  eprintf "%aThe identifier %s is not mutable.\n"
    output_location loc id;
  raise Toplevel
;;

let undefined_type_err ty_desc =
  eprintf "%tThe type %a is declared in the interface, but not implemented.\n"
    output_input_name output_type ty_desc;
  raise Toplevel
;;

let undefined_value_err val_desc =
  eprintf "%tThe value %a is declared in the interface, but not implemented.\n"
    output_input_name output_value val_desc;
  raise Toplevel
;;

let type_mismatch_err val_desc val_desc' =
  eprintf "%tThe value %a is declared with type %a,\n\
           but defined with type %a.\n"
    output_input_name
    output_value val_desc
    output_schema val_desc.info.val_typ
    output_schema val_desc'.info.val_typ;
  raise Toplevel
;;

let cannot_generalize_err val_desc =
  eprintf "%tThe type inferred for the value %a,\n\
           that is, %a,\n\
           contains type variables that cannot be generalized.\n"
    output_input_name
    output_value val_desc
    output_schema val_desc.info.val_typ;
  raise Toplevel
;;

let label_multiply_defined_err exp lbl =
  eprintf "%aThe label %a is defined several times in this record.\n" 
    output_location exp.e_loc
    output_label lbl;
  raise Toplevel
;;

let label_undefined_err exp lbl =
  eprintf "%aThe label %a is not defined in this record.\n"
    output_location exp.e_loc
    output_label lbl;
  raise Toplevel
;;

let label_not_belong_err exp lbl ty =
  eprintf "%aThe label %a does not belong to the type %a.\n"
    output_location exp.e_loc
    output_label lbl
    output_type ty;
  raise Toplevel
;;

let label_not_mutable_err exp lbl =
  eprintf "%aThe label %a is not mutable.\n"
    output_location exp.e_loc
    output_label lbl;
  raise Toplevel
;;

let rec_unknown_size_err ty loc =
  eprintf "%aValues of type %a cannot be defined with a \"let rec\".\n"
    output_location loc
    output_one_type ty;
  raise Toplevel
;;

let non_constant_constr_err cstr loc =
  eprintf "%aThe constructor %a requires an argument.\n"
    output_location loc
    output_constr cstr;
  raise Toplevel
;;

let constant_constr_err cstr loc =
  eprintf "%aThe constant constructor %a cannot accept an argument.\n"
    output_location loc
    output_constr cstr;
  raise Toplevel
;;

let illegal_letrec_pat loc =
  eprintf "%aOnly variables are allowed as \
           left-hand sides of \"let rec\".\n"
    output_location loc;
  raise Toplevel
;;

let illegal_letrec_expr loc =
  eprintf "%aThis kind of expression is not allowed in \
           right-hand sides of \"let rec\".\n"
    output_location loc;
  raise Toplevel
;;

let illegal_type_redefinition loc ty_desc =
  eprintf "%aThe type %a is exported as an abstract type by this module\n\
           and defined several times in the implementation.\n\
           Please define it only once.\n"
    output_location loc
    output_type_constr ty_desc;
  raise Toplevel
;;

let type_decl_arity_err loc ty_desc1 ty_desc2 =
  eprintf "%aThe type %a has been declared with %d parameter(s)\n\
           but is here defined with %d parameter(s).\n"
    output_location loc
    output_type_constr ty_desc1
    ty_desc1.info.ty_arity
    ty_desc2.info.ty_arity;
  raise Toplevel
;;

let recursive_abbrev_err loc ty_cstr =
  eprintf "%aThe type abbreviation %a is a cyclic (infinite) type.\n"
    output_location loc 
    output_type_constr ty_cstr;
  raise Toplevel
;;

let partial_apply_warning loc =
  eprintf "%aWarning: this function application is partial,\n\
           maybe some arguments are missing.\n"
    output_location loc;
  flush stderr
;;

let unused_cases_warning loc =
  eprintf "%aWarning: this matching case is unused.\n"
    output_location loc;
  flush stderr
;;

let not_exhaustive_warning loc =
  eprintf "%aWarning: this matching is not exhaustive.\n"
    output_location loc;
  flush stderr
;;

let bad_format_letter loc letter =
  eprintf "%aBad format letter `%c'.\n"
    output_location loc letter;
  raise Toplevel
;;

let displacement_overflow () =
  eprintf "%tPhrase too large, a relative displacement has overflowed.\n"
    output_input_name;
  raise Toplevel
;;

let unused_open_warning modname =
  eprintf "%tWarning: useless #open on module \"%s\".\n"
    output_input_name modname;
  flush stderr
;;
(* Handling of debugging events *)

#open "lambda";;
#open "syntax";;
#open "location";;
#open "modules";;

let record_events = ref false;;

let before env {e_loc = Loc(p1,p2)} l =
  if !record_events then
    Levent({ev_kind = Lbefore;
            ev_file = (!defined_module).mod_name;
            ev_char = p1;
            ev_env = env;
            ev_pos = 0}, l)
  else l
;;

let after_pat env {p_loc = Loc(p1,p2)} l =
  if !record_events then
    Levent({ev_kind = Lbefore;
            ev_file = (!defined_module).mod_name;
            ev_char = p2;
            ev_env = env;
            ev_pos = 0}, l)
  else l
;;

let after env {e_loc = Loc(p1,p2); e_typ = ty} l =
  if !record_events then
    Levent({ev_kind = Lafter ty;
            ev_file = (!defined_module).mod_name;
            ev_char = p2;
            ev_env = env;
            ev_pos = 0}, l)
  else l
;;

let events = ref ([] : event list);;

let reset () =
  events := []
;;

let enter e =
  events := e :: !events
;;

let get_events () =
  let res = !events in events := []; res
;;
(* front.ml : translation abstract syntax -> extended lambda-calculus. *)

#open "misc";;
#open "const";;
#open "globals";;
#open "syntax";;
#open "builtins";;
#open "modules";;
#open "lambda";;
#open "prim";;
#open "matching";;
#open "tr_env";;
#open "trstream";;
#open "error";;

(* Propagation of constants *)

exception Not_constant;;

let extract_constant = function
    Lconst cst -> cst | _ -> raise Not_constant
;;

(* Compilation of let rec definitions *)

let rec check_letrec_expr expr =
  match expr.e_desc with
    Zident _ -> ()
  | Zconstant _ -> ()
  | Ztuple el -> do_list check_letrec_expr el
  | Zconstruct0 cstr -> ()
  | Zconstruct1(cstr, expr) ->
      check_letrec_expr expr;
      begin match cstr.info.cs_kind with
        Constr_superfluous n ->
          begin match expr.e_desc with
            Ztuple _ -> () | _ -> illegal_letrec_expr expr.e_loc
          end
      | _ -> ()
      end
  | Zfunction _ -> ()
  | Zconstraint(e,_) -> check_letrec_expr e
  | Zvector el -> do_list check_letrec_expr el
  | Zrecord lbl_expr_list ->
      do_list (fun (lbl,expr) -> check_letrec_expr expr) lbl_expr_list
  | Zlet(flag, pat_expr_list, body) ->
      do_list (fun (pat,expr) -> check_letrec_expr expr) pat_expr_list;
      check_letrec_expr body      
  | Zparser _ -> ()
  | _ ->
      illegal_letrec_expr expr.e_loc
;;

let rec size_of_expr expr =
  match expr.e_desc with
    Ztuple el ->
      do_list check_letrec_expr el; list_length el
  | Zconstruct1(cstr, expr) ->
      check_letrec_expr expr;
      begin match cstr.info.cs_kind with
        Constr_superfluous n -> n | _ -> 1
      end
  | Zfunction _ ->
      2
  | Zconstraint(e,_) ->
      size_of_expr e
  | Zvector el ->
      do_list check_letrec_expr el; list_length el
  | Zrecord lbl_expr_list ->
      do_list (fun (lbl,expr) -> check_letrec_expr expr) lbl_expr_list;
      list_length lbl_expr_list
  | Zlet(flag, pat_expr_list, body) ->
      do_list (fun (pat,expr) -> check_letrec_expr expr) pat_expr_list;
      size_of_expr body      
  | Zparser _ ->
      2
  | _ ->
      illegal_letrec_expr expr.e_loc
;;

(* Default cases for partial matches *) 

let partial_try = Lprim(Praise, [Lvar 0]);;

(* Optimisation of generic comparisons *)

let translate_compar gen_fun (int_comp, float_comp) ty arg1 arg2 =
  let comparison =
    if types__same_base_type ty type_int ||
       types__same_base_type ty type_char then
      Ptest int_comp
    else if types__same_base_type ty type_float then
      Ptest float_comp
    else match (int_comp, arg1, arg2) with
      (Pint_test PTeq, Lconst(SCblock(tag, [])), _) -> Ptest Peq_test
    | (Pint_test PTnoteq, Lconst(SCblock(tag, [])), _) -> Ptest Pnoteq_test
    | (Pint_test PTeq, _, Lconst(SCblock(tag, []))) -> Ptest Peq_test
    | (Pint_test PTnoteq, _, Lconst(SCblock(tag, []))) -> Ptest Pnoteq_test
    | _ -> Pccall(gen_fun, 2) in
  Lprim(comparison, [arg1; arg2])
;;

let comparison_table =
  ["equal",        (Pint_test PTeq, Pfloat_test PTeq);
   "notequal",     (Pint_test PTnoteq, Pfloat_test PTnoteq);
   "lessthan",     (Pint_test PTlt, Pfloat_test PTlt);
   "lessequal",    (Pint_test PTle, Pfloat_test PTle);
   "greaterthan",  (Pint_test PTgt, Pfloat_test PTgt);
   "greaterequal", (Pint_test PTge, Pfloat_test PTge)]
;;

(* Auxiliary to apply a superfluous constructor when the argument is an
   already-allocated tuple (in Lvar 0) *)

let alloc_superfluous_constr cstr n =
  let rec extract_fields i =
    if i >= n then [] else
      Lprim(Pfield i, [Lvar 0]) :: extract_fields (succ i) in
  Lprim(Pmakeblock cstr.info.cs_tag, extract_fields 0)
;;

(* Translation of expressions *)

let rec translate_expr env =
  let rec transl expr =
  match expr.e_desc with
    Zident(Ref(Zlocal s)) ->
      translate_access s env
  | Zident(Ref(Zglobal g)) ->
      (match g.info.val_prim with
        ValueNotPrim ->
          Lprim(Pget_global g.qualid, [])
      | ValuePrim(0, p) ->
          Lprim(Pget_global g.qualid, [])
      | ValuePrim(arity, p) ->
          let rec make_fct args n =
            if n >= arity
            then Lprim(p, args)
            else Lfunction(make_fct (Lvar n :: args) (n+1))
          in
            make_fct [] 0)
  | Zconstant cst ->
      Lconst cst
  | Ztuple(args) ->
      let tr_args =
        map transl args in
      begin try
        Lconst(SCblock(ConstrRegular(0,1), map extract_constant tr_args))
      with Not_constant ->
        Lprim(Pmakeblock(ConstrRegular(0,1)), tr_args)
      end
  | Zconstruct0(c) ->
      begin match c.info.cs_kind with
        Constr_constant ->
          Lconst(SCblock(c.info.cs_tag, []))
      | Constr_regular ->
          Lfunction(Lprim(Pmakeblock c.info.cs_tag, [Lvar 0]))
      | Constr_superfluous n ->
          Lfunction(alloc_superfluous_constr c n)
      end
  | Zconstruct1(c,arg) ->
      begin match c.info.cs_kind with
        Constr_superfluous n ->
          begin match arg.e_desc with
            Ztuple argl ->
              let tr_argl = map transl argl in
              begin try                           (* superfluous ==> pure *)
                Lconst(SCblock(c.info.cs_tag, map extract_constant tr_argl))
              with Not_constant ->
                Lprim(Pmakeblock c.info.cs_tag, tr_argl)
              end
          | _ ->
              Llet([transl arg], alloc_superfluous_constr c n)
          end
      | _ ->
          let tr_arg = transl arg in
          begin match c.info.cs_mut with
            Mutable ->
              Lprim(Pmakeblock c.info.cs_tag, [tr_arg])
          | Notmutable ->
              begin try
                Lconst(SCblock(c.info.cs_tag, [extract_constant tr_arg]))
              with Not_constant ->
                Lprim(Pmakeblock c.info.cs_tag, [tr_arg])
              end
          end
      end
  | Zapply({e_desc = Zfunction ((patl,_)::_ as case_list)} as funct, args) ->
      if list_length patl == list_length args then
        Llet(translate_let env args,
             translate_match expr.e_loc env case_list)
      else
      event__after env expr (Lapply(transl funct, map transl args))
  | Zapply({e_desc = Zident(Ref(Zglobal g))} as fct, args) ->
      begin match g.info.val_prim with
        ValueNotPrim ->
          event__after env expr (Lapply(transl fct, map transl args))
      | ValuePrim(arity, p) ->
          if arity == list_length args then
            match (p, args) with
              (Praise, [arg1]) ->
                Lprim(p, [event__after env arg1 (transl arg1)])
            | (Pccall(fn, _), [arg1; arg2]) ->
                begin try
                  translate_compar fn (assoc fn comparison_table)
                                   arg1.e_typ (transl arg1) (transl arg2)
                with Not_found ->
                  event__after env expr (Lprim(p, map transl args))
                end
            | (Pccall(_, _), _) ->
                event__after env expr (Lprim(p, map transl args))
            | (_, _) ->
                Lprim(p, map transl args)
          else
            event__after env expr (Lapply(transl fct, map transl args))
      end
  | Zapply(funct, args) ->
      event__after env expr (Lapply(transl funct, map transl args))
  | Zlet(false, pat_expr_list, body) ->
      let cas = map (fun (pat, _) -> pat) pat_expr_list in
        Llet(translate_bind env pat_expr_list,
             translate_match expr.e_loc env [cas, body])
  | Zlet(true, pat_expr_list, body) ->
      let new_env =
        add_let_rec_to_env env pat_expr_list in
      let translate_rec_bind (pat, expr) =
        (translate_expr new_env expr, size_of_expr expr) in
      Lletrec(map translate_rec_bind pat_expr_list,
              event__before new_env body (translate_expr new_env body))
  | Zfunction [] ->
      fatal_error "translate_expr: empty fun"
  | Zfunction((patl1,act1)::_ as case_list) ->
      let rec transl_fun debug_env = function
          [] ->
            translate_match expr.e_loc env case_list
        | pat::patl ->
            let new_debug_env =
              if pat_irrefutable pat
              then let (newenv, _, _) = add_pat_to_env debug_env pat in newenv
              else Treserved debug_env in
            Lfunction(event__after_pat new_debug_env pat
                        (transl_fun new_debug_env patl)) in
      transl_fun env patl1
  | Ztrywith(body, pat_expr_list) ->
      Lhandle(transl body,
              translate_simple_match env partial_try pat_expr_list)
  | Zsequence(e1, e2) ->
      Lsequence(transl e1, event__before env e2 (transl e2))
  | Zcondition(eif, ethen, eelse) ->
      Lifthenelse(transl eif,
                  event__before env ethen (transl ethen),
                  if match eelse.e_desc with
                       Zconstruct0(cstr) -> cstr == constr_void | _ -> false
                  then transl eelse
                  else event__before env eelse (transl eelse))
  | Zwhile(econd, ebody) ->
      Lwhile(transl econd, event__before env ebody (transl ebody))
  | Zfor(id, estart, estop, up_flag, ebody) ->
      let new_env = add_for_parameter_to_env env id in
      Lfor(transl estart,
           translate_expr (Treserved env) estop,
           up_flag,
           event__before new_env ebody (translate_expr new_env ebody))
  | Zconstraint(e, _) ->
      transl e
  | Zvector [] ->
      Lconst(SCblock(ConstrRegular(0,0), []))
  | Zvector args ->
      Lprim(Pmakeblock (ConstrRegular(0,0)), map transl args)
  | Zassign(id, e) ->
      translate_update id env (transl e)
  | Zrecord lbl_expr_list ->
      let v = make_vect (list_length lbl_expr_list) (Lconst const_unit) in
        do_list
          (fun (lbl, e) -> v.(lbl.info.lbl_pos) <- transl e)
          lbl_expr_list;
        begin try
          if for_all
               (fun (lbl, e) -> lbl.info.lbl_mut == Notmutable)
               lbl_expr_list
          then Lconst(SCblock(ConstrRegular(0,0),
                              map_vect_list extract_constant v))
          else raise Not_constant
        with Not_constant ->
          Lprim(Pmakeblock(ConstrRegular(0,0)), list_of_vect v)
        end
  | Zrecord_access (e, lbl) ->
      Lprim(Pfield lbl.info.lbl_pos, [transl e])
  | Zrecord_update (e1, lbl, e2) ->
      Lprim(Psetfield lbl.info.lbl_pos, [transl e1; transl e2])
  | Zstream stream_comp_list ->
      translate_stream translate_expr env stream_comp_list
  | Zparser case_list ->
      let (stream_type, _) = types__filter_arrow expr.e_typ in
      translate_parser translate_expr expr.e_loc env case_list stream_type
  | Zwhen(e1,e2) ->
      fatal_error "front: Zwhen"
  in transl

and transl_action env (patlist, expr) =
  let (new_env, add_lets, num_pops) = add_pat_list_to_env env patlist in
  let action =
    match expr.e_desc with
      Zwhen(e1, e2) ->
        guard_expression
          (translate_expr new_env e1) (translate_expr new_env e2) num_pops
    | _ ->
        translate_expr new_env expr in
  (patlist, add_lets(event__before new_env expr action))

and translate_match loc env casel =
  translate_matching_check_failure loc (map (transl_action env) casel)

and translate_simple_match env failure_code pat_expr_list =
  translate_matching failure_code
    (map (fun (pat, expr) -> transl_action env ([pat], expr)) pat_expr_list)

and translate_let env = function
     [] ->  []
  | a::l -> translate_expr env a :: translate_let (Treserved env) l

and translate_bind env = function
    [] -> []
  | (pat, expr) :: rest ->
      translate_expr env expr :: translate_bind (Treserved env) rest
;;

(* Translation of toplevel expressions *)

let translate_expression = translate_expr Tnullenv
;;

(* Translation of toplevel let expressions *)

let rec make_sequence f = function
    [] -> Lconst(SCatom(ACint 0))
  | [x] -> f x
  | x::rest -> Lsequence(f x, make_sequence f rest)
;;

let translate_letdef loc pat_expr_list =
  let modname = (!defined_module).mod_name in
  match pat_expr_list with
    [{p_desc = Zvarpat i}, expr] ->      (* Simple case: let id = expr *)
      Lprim(Pset_global {qual=modname; id=i}, [translate_expression expr])
  | _ ->                                 (* The general case *)
    let pat_list =
      map (fun (p, _) -> p) pat_expr_list in
    let vars =
      flat_map free_vars_of_pat pat_list in
    let env =
      env_for_toplevel_let pat_list in
    let store_global var =
      Lprim(Pset_global {qual=modname; id=var},
            [translate_access var env]) in
    Llet(translate_bind Tnullenv pat_expr_list,
         translate_matching_check_failure
           loc [pat_list, make_sequence store_global vars])
;;

(* Translation of toplevel let rec expressions *)

let extract_variable pat =
  let rec extract p =
    match p.p_desc with
      Zvarpat id -> id
    | Zconstraintpat(p, ty) -> extract p
    | _ -> illegal_letrec_pat pat.p_loc
  in extract pat
;;

exception Complicated_definition;;

let translate_letdef_rec loc pat_expr_list =
  (* First check that all patterns are variables *)
  let var_expr_list =
    map (fun (pat, expr) -> (extract_variable pat, expr)) pat_expr_list in
  let modname = (!defined_module).mod_name in
  try                                   (* Simple case: let rec id = fun *)
    make_sequence
      (function (i, e) ->
        match e.e_desc with
          Zfunction _ ->
            Lprim(Pset_global {qual=modname; id=i}, [translate_expression e])
        | _ ->
            raise Complicated_definition)
      var_expr_list
  with Complicated_definition ->        (* The general case *)
    let dummies =
      make_sequence
        (function (i, e) ->
          Lprim (Pset_global {qual=modname; id=i},
                 [Lprim(Pdummy(size_of_expr e), [])]))
        var_expr_list in
    let updates =
      make_sequence
        (function (i, e) ->
          Lprim(Pupdate, [Lprim(Pget_global {qual=modname; id=i}, []);
                          translate_expression e]))
        var_expr_list in
    Lsequence(dummies, updates)
;;
(* Global symbol tables *)

#open "const";;
#open "prim";;

(* A reference to a global, in a source file, is either a qualified identifier
   mod__name, or an unqualified identifier name. *)

type global_reference =
    GRname of string
  | GRmodname of qualified_ident
;;

(* Internally, a global is represented by its fully qualified name,
   plus associated information. *)

type 'a global =
  { qualid: qualified_ident; (* Full name *)
    info: 'a }               (* Description *)
;;

let little_name_of_global g = g.qualid.id
;;

(* Type constructors *)

type type_constr =
  { mutable ty_stamp: int;              (* Stamp *)
    mutable ty_abbr: type_abbrev }      (* Abbreviation or not *)

and type_abbrev =
    Tnotabbrev
  | Tabbrev of typ list * typ           (* Parameters and body *)

(* Type expressions *)

and typ =
  { typ_desc: typ_desc;                 (* What kind of type expression? *)
    mutable typ_level: int }            (* Binding level *)
and typ_desc =
    Tvar of mutable typ_link            (* A type variable *)
  | Tarrow of typ * typ                 (* A function type *)
  | Tproduct of typ list                (* A tuple type *)
  | Tconstr of type_constr global * typ list  (* A constructed type *)
and typ_link =
    Tnolink                             (* Free variable *)
  | Tlinkto of typ                      (* Instantiated variable *)
;;

(* Type constructor descriptions *)

type type_desc =
  { ty_constr: type_constr global;      (* The constructor *)
    ty_arity: int;                      (* Its arity *)
    mutable ty_desc: type_components }  (* Its description *)

and type_components =
    Abstract_type
  | Variant_type of constr_desc global list (* Sum type -> list of constr. *)
  | Record_type of label_desc global list (* Record type -> list of labels *)
  | Abbrev_type of typ list * typ         (* Abbreviation *)

(* Value constructors *)

and constr_desc =
  { cs_res: typ;                       (* Result type *)
    cs_arg: typ;                       (* Argument type *)
    cs_mut: mutable_flag;              (* Mutable or not *)
    cs_tag: constr_tag;                (* Its run-time tag *)
    cs_kind: constr_kind }             (* How it is represented *)

and mutable_flag =
  Mutable | Notmutable

and constr_kind =
    Constr_constant                     (* Constant constructor *)
  | Constr_regular                      (* Usual constructor *)
  | Constr_superfluous of int           (* Superfluous constructor
                                           with its arity *)

(* Labels *)

and label_desc =
  { lbl_res: typ;                      (* Result type *)
    lbl_arg: typ;                      (* Argument type *)
    lbl_mut: mutable_flag;             (* Mutable or not *)
    lbl_pos: int }                     (* Position in the tuple *)
;;

let generic = (-1)
and notgeneric = 0;;

let no_type = { typ_desc = Tproduct []; typ_level = 0 };;

(* Global variables *)

type value_desc =
  { val_typ: typ;                       (* Type *)
    val_prim: prim_desc }               (* Is this a primitive? *)

and prim_desc =
    ValueNotPrim
  | ValuePrim of int * primitive        (* arity & implementation *)
;;

(* The type of the instructions of the abstract machine *)

#open "const";;
#open "prim";;

type zam_instruction =
    Kquote of struct_constant 
  | Kget_global of qualified_ident
  | Kset_global of qualified_ident
  | Kaccess of int
  | Kgrab
  | Kpush
  | Kpushmark
  | Klet
  | Kendlet of int
  | Kapply
  | Ktermapply
  | Kcheck_signals
  | Kreturn
  | Kclosure of int
  | Kletrec1 of int
  | Kmakeblock of constr_tag * int 
  | Kprim of primitive 
  | Kpushtrap of int
  | Kpoptrap
  | Klabel of int
  | Kbranch of int
  | Kbranchif of int
  | Kbranchifnot of int
  | Kstrictbranchif of int
  | Kstrictbranchifnot of int
  | Ktest of bool_test * int
  | Kbranchinterval of int * int * int * int
  | Kswitch of int vect
  | Kevent of lambda__event
;;

type zam_phrase =
  { kph_rec: bool;                      (* is this a recursive let? *)
    kph_init: zam_instruction list;     (* initialization code *)
    kph_fcts: zam_instruction list }    (* code for functions *)
;;

let Nolabel = (-1)
;;
(* Internationalization (translation of error messages) *)

#open "misc";;

let language = ref "";;

let read_transl_file msgfile =
  let ic = open_in msgfile in
  let tag_buffer = create_string 16
  and msg_buffer = create_string 1024 in
  let rec store_tag c i =
    if i >= 16 then i else (tag_buffer.[i] <- c; succ i)
  and store_msg c i =
    if i >= 1024 then i else (msg_buffer.[i] <- c; succ i)
  and read_line i =
    match input_char ic with
      `\n` -> i
    | `\\` -> begin match input_char ic with
                `\\` -> read_line(store_msg `\\` i)
              | `n`  -> read_line(store_msg `\n` i)
              | `\n` -> skip_blanks i
              | c    -> read_line(store_msg c (store_msg `\\` i))
              end
    | c    -> read_line(store_msg c i)
  and skip_blanks i =
    match input_char ic with
      ` `|`\t` -> skip_blanks i
    | c        -> read_line(store_msg c i)
  and read_tag i =
    match input_char ic with
      `:`           -> (i, skip_blanks 0)
    | ` `|`\n`|`\t` -> read_tag i
    | c             -> read_tag(store_tag c i) in
  let transl_tbl = hashtbl__new 37 in
  let currsrc = ref "" in
  begin try
    while true do
      let (tag_len, msg_len) = read_tag 0 in
      if sub_string tag_buffer 0 tag_len = "src" then
        currsrc := sub_string msg_buffer 0 msg_len
      else if sub_string tag_buffer 0 tag_len = !language then
        hashtbl__add transl_tbl !currsrc (sub_string msg_buffer 0 msg_len)
      else ()
    done
  with End_of_file ->
    close_in ic
  end;
  transl_tbl
;;

type translation_table =
    Unknown
  | None
  | Transl of (string, string) hashtbl__t;;

let transl_table = ref Unknown;;

let rec translate msg =
  match !transl_table with
    None ->
      msg
  | Transl tbl ->
      begin try hashtbl__find tbl msg with Not_found -> msg end
  | Unknown ->
      transl_table :=
        if string_length !language == 0 then
          None
        else begin
          try
            Transl(read_transl_file(find_in_path "camlmsgs.txt"))
          with Cannot_find_file _ | sys__Sys_error _ | sys__Break ->
            None
        end;
      translate msg
;;

let fprintf oc (fmt : ('a, out_channel, unit) printf__format) =
  printf__fprintf oc
    (obj__magic(translate(obj__magic fmt : string)) :
                                ('a, out_channel, unit) printf__format)
;;

let printf fmt = fprintf std_out fmt
and eprintf fmt = fprintf std_err fmt
;;

(* Handlings of local labels and backpatching *)

#open "misc";;
#open "instruct";;
#open "buffcode";;

type label_definition =
    Label_defined of int
  | Label_undefined of (int * int) list
;;

let label_table  = ref ([| |] : label_definition vect)
;;

let reset_label_table () =
  label_table := (make_vect 16 (Label_undefined [])); ()
;;

let extend_label_table needed =
  let old = vect_length !label_table in
  let new_table = make_vect ((needed / old + 1) * old) (Label_undefined []) in
  for i = 0 to pred old do
    new_table.(i) <- (!label_table).(i)
  done;
  label_table := new_table; ()
;;

let define_label lbl =
  if lbl >= vect_length !label_table then extend_label_table lbl;
  match (!label_table).(lbl) with
    Label_defined _ ->
      fatal_error "define_label : already defined"
  | Label_undefined l ->
      let currpos = !out_position in
        (!label_table).(lbl) <- (Label_defined currpos);
        match l with
            [] -> ()
          |  _ -> do_list (fun (pos,orig) -> out_position := pos;
                                             out_short (currpos - orig)) l;
                  out_position := currpos
;;

let out_label_with_orig orig lbl =
  if lbl == Nolabel then fatal_error "out_label: undefined label";
  if lbl >= vect_length !label_table then extend_label_table lbl;
  match (!label_table).(lbl) with
    Label_defined def ->
      out_short (def - orig)
  | Label_undefined l ->
      (!label_table).(lbl) <-
        Label_undefined((!out_position, orig) :: l);
      out_short 0
;;

let out_label l = out_label_with_orig !out_position l
;;



