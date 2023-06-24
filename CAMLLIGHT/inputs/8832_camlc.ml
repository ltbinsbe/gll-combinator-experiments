(*  back.ml : translation of lambda terms to lists of instructions. *)

#open "misc";;
#open "const";;
#open "lambda";;
#open "prim";;
#open "instruct";;

(* "is_return" determines if we're in tail call position. *)

let rec is_return = function
    Kreturn :: _ -> true
  | Klabel lbl :: c -> is_return c
  | Kevent e :: c -> is_return c
  | _ -> false
;;

(* Label generation *)

let label_counter = ref 0;;

let reset_label () =
  label_counter := 0
and new_label () =
  incr label_counter; !label_counter
;;

(* Add a label to a list of instructions. *)

let label_code = function
    Kbranch lbl :: _ as code ->
      (lbl, code)
  | Klabel lbl :: _ as code ->
      (lbl, code)
  | code ->
      let lbl = new_label() in
        (lbl, Klabel lbl :: code)
;;

(* Generate a branch to the given list of instructions. *)

let make_branch = function
    Kreturn :: _ as code ->
      (Kreturn, code)
  | (Kbranch _ as branch) :: _ as code ->
      (branch, code)
  | code ->
      let lbl = new_label() in
        (Kbranch lbl, Klabel lbl :: code)
;;

(* Discard all instructions up to the next label. *)

let rec discard_dead_code = function
    [] -> []
  | Klabel _ :: _ as code -> code
  | Kset_global _ :: _ as code -> code
  | _ :: rest -> discard_dead_code rest
;;

(* Generate a jump through table, unless unnecessary. *)

let add_switchtable switchtable code =
  try
    for i = 1 to vect_length switchtable - 1 do
      if switchtable.(i) != switchtable.(0) then raise Exit
    done;
    match code with
      Klabel lbl :: code1 ->
        if lbl == switchtable.(0) then code
        else Kbranch switchtable.(0) :: code
    | _ ->
        Kbranch switchtable.(0) :: code
  with Exit ->
    Kswitch switchtable :: code
;;

(* Compiling N-way integer branches *)

(* Input: a list of (key, action) pairs, where keys are integers. *)
(* Output: a decision tree with the format below *)

type decision_tree =
    DTfail
  | DTinterval of decision_tree * decision * decision_tree

and decision =
  { low: int;
    act: lambda vect;
    high: int }
;;

let compile_nbranch int_of_key casel =
  let casei =
    map (fun (key, act) -> (int_of_key key, act)) casel in
  let cases =
    sort__sort (fun (key1,act1) (key2,act2) -> key1 <= key2) casei in
  let keyv =
    vect_of_list (map fst cases)
  and actv =
    vect_of_list (map snd cases) in
  let n =
    vect_length keyv in
  let extract_act start stop =
    let v =
      make_vect (keyv.(stop) - keyv.(start) + 1) (Lstaticfail 0) in
    for i = start to stop do
      v.(keyv.(i) - keyv.(start)) <- actv.(i)
    done;
    v in
  (* Now we partition the set of keys keyv into maximal dense enough segments.
     A segment is dense enough if its span (max point - min point) is
     less than four times its size (number of points). *)
  let rec partition start =
    if start >= n then [] else
    let stop = ref (n-1) in
    while keyv.(!stop) - keyv.(start) >= 255 ||
          keyv.(!stop) - keyv.(start) > 4 * (!stop - start) do
      decr stop
    done;
    (* We've found a dense enough segment.
       In the worst case, !stop = start and the segment is a single point *)
    (* Now build the vector of actions *)
    { low = keyv.(start);
      act = extract_act start !stop;
      high = keyv.(!stop) } :: partition (!stop + 1) in
  let part =
    vect_of_list (partition 0) in
  (* We build a balanced binary tree *)
  let rec make_tree start stop =
    if start > stop then
      DTfail
    else
      let middle = (start + stop) / 2 in
        DTinterval(make_tree start (middle-1),
                   part.(middle), 
                   make_tree (middle+1) stop) in
  make_tree 0 (vect_length part - 1)
;;

(* To check if a switch construct contains tags that are unknown at
   compile-time (i.e. exception tags). *)

let switch_contains_extensibles casel =
  exists (function ConstrExtensible _, _ -> true | _ -> false) casel
;;

(* Inversion of a boolean test ( < becomes >= and so on) *)

let invert_bool_test =
  let invert_prim_test = function
      PTeq -> PTnoteq
    | PTnoteq -> PTeq
    | PTnoteqimm x -> fatal_error "invert_prim_test"
    | PTlt -> PTge
    | PTle -> PTgt
    | PTgt -> PTle
    | PTge -> PTlt in
  function
      Peq_test -> Pnoteq_test
    | Pnoteq_test -> Peq_test
    | Pint_test t -> Pint_test(invert_prim_test t)
    | Pfloat_test t -> Pfloat_test(invert_prim_test t)
    | Pstring_test t -> Pstring_test(invert_prim_test t)
    | Pnoteqtag_test t -> fatal_error "invert_prim_test2"
;;

(* Production of an immediate test *)

let test_for_atom = function
    ACint x -> Pint_test(PTnoteqimm x)
  | ACchar x -> Pint_test(PTnoteqimm (int_of_char x))
  | ACfloat x -> Pfloat_test(PTnoteqimm x)
  | ACstring x -> Pstring_test(PTnoteqimm x)
;;

(* To keep track of function bodies that remain to be compiled. *)

let still_to_compile  = (stack__new () : (lambda * int) stack__t);;

(* The translator from lambda terms to lists of instructions.

   staticfail : the label where Lstaticfail must branch.
   lambda : the lambda term to compile.
   code : the continuation, i.e. the code that follows the code for lambda.

   The tests on the continuation detect tail-calls and avoid jumps to jumps,
   or jumps to function returns.

*)

let rec compile_expr staticfail =
  let rec compexp expr code = match expr with
    Lvar n ->
        Kaccess n :: code
  | Lconst cst ->
       (match code with
          (Kquote _ | Kget_global _ | Kaccess _ | Kpushmark) :: _ -> code
        | _ -> Kquote cst :: code)
  | Lapply(body, args) ->
        if is_return code then
          compexplist args (Kpush ::
            compexp body (Ktermapply :: discard_dead_code code))
        else
          Kpushmark ::
          compexplist args (Kpush :: compexp body (Kapply :: code))
  | Lfunction body ->
        if is_return code then
          Kgrab :: compexp body code
        else begin
          let lbl = new_label() in
            stack__push (body, lbl) still_to_compile;
            Kclosure lbl :: code
          end
  | Llet(args, body) ->
        let code1 = if is_return code then code
                    else Kendlet(list_length args) :: code in
        let rec comp_args = function
            [] ->
              compexp body code1
	  | exp::rest ->
              compexp exp (Klet :: comp_args rest) in
        comp_args args
  | Lletrec([Lfunction f, _], body) ->
        let code1 = if is_return code then code else Kendlet 1 :: code in
        let lbl = new_label() in
          stack__push (f, lbl) still_to_compile;
          Kletrec1 lbl :: compexp body code1
  | Lletrec(args, body) ->
        let size = list_length args in
        let code1 = if is_return code then code else Kendlet size :: code in
	let rec comp_args i = function
	    [] ->
              compexp body code1
	  | (exp, sz)::rest ->
              compexp exp (Kpush :: Kaccess i :: Kprim Pupdate ::
                            comp_args (i-1) rest) in
        list_it
          (fun (e, sz) code -> Kprim(Pdummy sz) :: Klet :: code)
          args (comp_args (size-1) args)
  | Lprim(Pget_global qualid, []) ->
        Kget_global qualid :: code
  | Lprim(Pset_global qualid, [exp]) ->
        compexp exp (Kset_global qualid :: code)
  | Lprim(Pmakeblock tag, explist) ->
        compexplist explist (Kmakeblock(tag, list_length explist) :: code)
  | Lprim(Pnot, [exp]) ->
       (match code with
          Kbranchif lbl :: code' ->
            compexp exp (Kbranchifnot lbl :: code')
        | Kbranchifnot lbl :: code' ->
            compexp exp (Kbranchif lbl :: code')
        | _ ->
            compexp exp (Kprim Pnot :: code))
  | Lprim(Psequand, [exp1; exp2]) ->
       (match code with
          Kbranch lbl :: _  ->
            compexp exp1 (Kstrictbranchifnot lbl :: compexp exp2 code)
        | Kbranchifnot lbl :: _ ->
            compexp exp1 (Kbranchifnot lbl :: compexp exp2 code)
        | Kbranchif lbl :: code' ->
            let lbl1, code1 = label_code code' in
              compexp exp1 (Kbranchifnot lbl1 ::
                            compexp exp2 (Kbranchif lbl :: code1))
        | _ ->
            let lbl = new_label() in
              compexp exp1 (Kstrictbranchifnot lbl ::
                            compexp exp2 (Klabel lbl :: code)))
  | Lprim(Psequor, [exp1; exp2]) ->
       (match code with
          Kbranch lbl :: _  ->
            compexp exp1 (Kstrictbranchif lbl :: compexp exp2 code)
        | Kbranchif lbl :: _  ->
            compexp exp1 (Kbranchif lbl :: compexp exp2 code)
        | Kbranchifnot lbl :: code' ->
            let lbl1, code1 = label_code code' in
              compexp exp1 (Kbranchif lbl1 ::
                            compexp exp2 (Kbranchifnot lbl :: code1))
        | _ ->
            let lbl = new_label() in
              compexp exp1 (Kstrictbranchif lbl ::
                            compexp exp2 (Klabel lbl :: code)))

  | Lprim((Ptest tst as p), explist) ->
       (match code with
          Kbranchif lbl :: code' ->
            compexplist explist (Ktest(tst,lbl) :: code')
        | Kbranchifnot lbl :: code' ->
            compexplist explist (Ktest(invert_bool_test tst,lbl) :: code')
        | _ ->
            compexplist explist (Kprim p :: code))
  | Lprim(Praise, explist) ->
        compexplist explist (Kprim Praise :: discard_dead_code code)
  | Lprim(p, explist) ->
        compexplist explist (Kprim p :: code)
  | Lstatichandle(body, Lstaticfail 0) ->
        compexp body code
  | Lstatichandle(body, handler) ->
        let branch1, code1 = make_branch code
        and lbl2 = new_label() in
          compile_expr lbl2 body
                       (branch1 :: Klabel lbl2 :: compexp handler code1)
  | Lstaticfail n ->
        let c = Kbranch staticfail :: discard_dead_code code in
        if n = 0 then c else Kendlet n :: c
  | Lhandle(body, handler) ->
        let branch1, code1 = make_branch code in
        let lbl2 = new_label() in
        let code2 = if is_return code1 then code1 else Kendlet 1 :: code1 in
          Kpushtrap lbl2 ::
            compexp body
                    (Kpoptrap :: branch1 :: Klabel lbl2 ::
                       compexp handler code2)
  | Lifthenelse(cond, ifso, ifnot) ->
        comp_test2 cond ifso ifnot code
  | Lsequence(exp1, exp2) ->
        compexp	exp1 (compexp exp2 code)
  | Lwhile(cond, body) ->
        let lbl1 = new_label() and lbl2 = new_label() in
          Kbranch lbl1 :: Klabel lbl2 :: Kcheck_signals ::
          compexp body (Klabel lbl1 :: compexp cond (
            Kbranchif lbl2 :: Kquote(const_unit) :: code))
  | Lfor(start, stop, up_flag, body) ->
        let lbl_end = new_label()
        and lbl_loop = new_label() in
          compexp start (
            Kmakeblock(ConstrRegular(0,1), 1) :: Klet ::
            compexp stop (
              Klet :: Klabel lbl_loop :: Kcheck_signals ::
              Kaccess 1 :: Kprim(Pfield 0) :: Klet :: 
              Kpush :: Kaccess 1 ::
              Ktest(Pint_test(if up_flag then PTlt else PTgt), lbl_end) ::
              compexp body (
                Kendlet 1 ::
                Kaccess 1 :: Kprim(if up_flag then Pincr else Pdecr) ::
                Kbranch lbl_loop ::
                Klabel lbl_end :: Kendlet 3 ::
                Kquote(const_unit) :: code)))
  | Lcond(arg, casel) ->
        let code1 =
          if match casel with
            (ACint _, _) :: _ :: _ -> true
          | (ACchar _, _) :: _ :: _ -> true
          | _ -> false
          then
            comp_decision (compile_nbranch int_of_atom casel) code
          else
            comp_tests (map (fun (cst,act) -> (test_for_atom cst, act)) casel)
                       code
        in
          compexp arg code1

  | Lswitch(1, arg, [ConstrRegular(_,_), exp]) ->
        compexp exp code
        (* This assumes that the argument has no side-effects.
           It holds for the switches generated by the pattern-matcher. *)
  | Lswitch(2, arg, [ConstrRegular(0,_), exp0]) ->
        compexp arg (Kbranchif staticfail :: compexp exp0 code)
  | Lswitch(2, arg, [ConstrRegular(1,_), exp1]) ->
        compexp arg (Kbranchifnot staticfail :: compexp exp1 code)
  | Lswitch(2, arg, [ConstrRegular(0,_), exp0; ConstrRegular(1,_), exp1]) ->
        comp_test2 arg exp1 exp0 code
  | Lswitch(2, arg, [ConstrRegular(1,_), exp1; ConstrRegular(0,_), exp0]) ->
        comp_test2 arg exp1 exp0 code
  | Lswitch(size, arg, casel) ->
        let code1 =
          if switch_contains_extensibles casel then
            comp_tests
              (map (fun (tag,act) -> (Pnoteqtag_test tag, act)) casel) code
          else if list_length casel >= size - 5 then
            Kprim Ptag_of :: comp_direct_switch size casel code
          else
            Kprim Ptag_of ::
              comp_decision (compile_nbranch int_of_constr_tag casel) code
       in
         compexp arg code1
  | Lshared(expr, lbl_ref) ->
       if !lbl_ref == Nolabel then begin
         let lbl = new_label() in
           lbl_ref := lbl;
           Klabel lbl :: compexp expr code
       end else begin
         Kbranch !lbl_ref :: discard_dead_code code
       end
  | Levent(event, expr) ->
       begin match event.ev_kind with
         Lbefore ->
           Kevent event :: compexp expr code
       | Lafter ty ->                 (* expr is either raise arg or apply *)
           if is_return code
           then compexp expr code (* don't destroy tail call opt. *)
           else compexp expr (Kevent event :: code)
       end

  and compexplist = fun
      [] code -> code
    | [exp] code -> compexp exp code
    | (exp::rest) code -> compexplist rest (Kpush :: compexp exp code)

  and comp_test2 cond ifso ifnot code =
    let branch1, code1 = make_branch code
    and lbl2 = new_label() in
      compexp cond
              (Kbranchifnot lbl2 ::
                 compexp ifso (branch1 :: Klabel lbl2 :: compexp ifnot code1))

  and comp_tests casel code =
    let branch1, code1 =
      make_branch code in
    let rec comp = function
        [] ->
          fatal_error "comp_tests"
      | [test,exp] ->
          Ktest(test, staticfail) :: compexp exp code1
      | (test,exp)::rest ->
          let lbl = new_label() in
            Ktest(test, lbl) ::
              compexp exp (branch1 :: Klabel lbl :: comp rest)
    in comp casel

  and comp_switch v branch1 code =
      let switchtable =
        make_vect (vect_length v) staticfail in
      let rec comp_cases n =
        if n >= vect_length v then
          code
        else begin
          let (lbl, code1) =
            label_code (compexp v.(n) (branch1 :: comp_cases (n+1))) in
          switchtable.(n) <- lbl;
          code1
        end in
      add_switchtable switchtable (discard_dead_code(comp_cases 0))

  and comp_decision tree code =
    let branch1, code1 = make_branch code in
    let rec comp_dec = fun
      (DTfail) code ->
        Kbranch staticfail :: discard_dead_code code
    | (DTinterval(left, dec, right)) code ->
        let (lbl_right, coderight) =
          match right with
            DTfail -> (staticfail, code)
          | _      -> label_code (comp_dec right code) in
        let (lbl_left, codeleft) =
          match left with
            DTfail -> (staticfail, coderight)
          | _ ->      label_code (comp_dec left coderight) in
        Kbranchinterval(dec.low, dec.high, lbl_left, lbl_right) ::
        begin match vect_length dec.act with
                1 -> compexp dec.act.(0) (branch1 :: codeleft)
              | _ -> comp_switch dec.act branch1 codeleft
        end in
    comp_dec tree code1

  and comp_direct_switch size casel code =
    let branch1, code1 = make_branch code in
    let switchtable = make_vect size staticfail in
    let rec comp_case = function
        [] ->
          fatal_error "comp_switch"
      | [tag, exp] ->
          let (lbl, code2) = label_code (compexp exp code1) in
          switchtable.(int_of_constr_tag tag) <- lbl;
          code2
      | (tag, exp) :: rest ->
          let (lbl, code2) =
            label_code (compexp exp (branch1 :: comp_case rest)) in
          switchtable.(int_of_constr_tag tag) <- lbl;
          code2
    in
      add_switchtable switchtable (discard_dead_code(comp_case casel))

  in compexp
;;

let rec compile_rest code =
  try
    let (exp, lbl) = stack__pop still_to_compile in
      compile_rest (Klabel lbl :: compile_expr Nolabel exp (Kreturn :: code))
  with stack__Empty ->
    code
;;

let compile_lambda (rec_flag : bool) expr =
  stack__clear still_to_compile;
  reset_label();
  let init_code =
    compile_expr Nolabel expr [] in
  let function_code =
    compile_rest [] in
  { kph_rec = rec_flag; kph_init = init_code; kph_fcts = function_code }
;;
(* To buffer bytecode during emission *)

let out_buffer = ref (create_string 64)
and out_position = ref 0
;;

let realloc_out_buffer () =
  let new_buffer = create_string (2 * string_length !out_buffer) in
    replace_string new_buffer !out_buffer 0;
    out_buffer := new_buffer;
    ()
;;

let init_out_code () =
  out_position := 0;
  ()
;;

let out b =
  if !out_position >= string_length !out_buffer then realloc_out_buffer();
  set_nth_char !out_buffer !out_position (fchar__char_of_int b);
  incr out_position
;;

let out_short s =
  if s >= 32768 || s < -32768 then
    error__displacement_overflow ()
  else begin
    out s; out (lshift_right s 8)
  end
;;

(* builtins.ml : the pre-defined global identifiers *)

#open "const";;
#open "globals";;
#open "modules";;

let builtin n d = {qualid={qual="builtin"; id=n}; info=d}
;;

(* Some types that must be known to the type checker *)

let constr_type_unit =
  builtin "unit" {ty_stamp=2; ty_abbr=Tnotabbrev}
and constr_type_exn =
  builtin "exn" {ty_stamp=3; ty_abbr=Tnotabbrev}
and constr_type_bool =
  builtin "bool" {ty_stamp=4; ty_abbr=Tnotabbrev}
and constr_type_int =
  builtin "int" {ty_stamp=5; ty_abbr=Tnotabbrev}
and constr_type_float =
  builtin "float" {ty_stamp=6; ty_abbr=Tnotabbrev}
and constr_type_string =
  builtin "string" {ty_stamp=7; ty_abbr=Tnotabbrev}
and constr_type_char =
  builtin "char" {ty_stamp=8; ty_abbr=Tnotabbrev}
and constr_type_list =
  builtin "list" {ty_stamp=9; ty_abbr=Tnotabbrev}
and constr_type_vect =
  builtin "vect" {ty_stamp=10; ty_abbr=Tnotabbrev}
and constr_type_option =
  builtin "option" {ty_stamp=11; ty_abbr=Tnotabbrev}
and constr_type_stream =
  {qualid = {qual="stream"; id="stream"};
   info   = {ty_stamp=1; ty_abbr=Tnotabbrev}}
    (* This assumes that "stream" is the first type defined in "stream". *)
and constr_type_format =
  {qualid = {qual="printf"; id="format"};
   info   = {ty_stamp=1; ty_abbr=Tnotabbrev}}
    (* This assumes that "format" is the first type defined in "printf". *)
and constr_type_num =
  (* This is needed only for the Windows port. *)
  {qualid = {qual="num"; id="num"};
   info   = {ty_stamp=1; ty_abbr=Tnotabbrev}}
    (* This assumes that "num" is the first type defined in "num". *)
;;

let type_arrow (t1,t2) =
  {typ_desc=Tarrow(t1, t2); typ_level=notgeneric}
and type_product tlist =
  {typ_desc=Tproduct(tlist); typ_level=notgeneric}
and type_unit =
  {typ_desc=Tconstr(constr_type_unit, []); typ_level=notgeneric}
and type_exn =
  {typ_desc=Tconstr(constr_type_exn, []); typ_level=notgeneric}
and type_bool =
  {typ_desc=Tconstr(constr_type_bool, []); typ_level=notgeneric}
and type_int =
  {typ_desc=Tconstr(constr_type_int, []); typ_level=notgeneric}
and type_float =
  {typ_desc=Tconstr(constr_type_float, []); typ_level=notgeneric}
and type_string =
  {typ_desc=Tconstr(constr_type_string, []); typ_level=notgeneric}
and type_char =
  {typ_desc=Tconstr(constr_type_char, []); typ_level=notgeneric}
and type_vect t =
  {typ_desc=Tconstr(constr_type_vect, [t]); typ_level=notgeneric}
and type_stream t =
  {typ_desc=Tconstr(constr_type_stream, [t]); typ_level=notgeneric}
and type_format t1 t2 t3 =
  {typ_desc=Tconstr(constr_type_format, [t1;t2;t3]); typ_level=notgeneric}
and type_num =
  {typ_desc=Tconstr(constr_type_num, []); typ_level=notgeneric}
;;

(* Some constructors that must be known to the parser *)

let constr_void =
  builtin "()"
    { cs_res = {typ_desc=Tconstr(constr_type_unit,[]); typ_level=notgeneric};
      cs_arg = type_unit;
      cs_tag = ConstrRegular(0,1);
      cs_mut = Notmutable;
      cs_kind= Constr_constant }
;;

let constr_nil =
  let arg = {typ_desc=Tvar(Tnolink); typ_level=generic} in
  builtin "[]"
    { cs_res = {typ_desc=Tconstr(constr_type_list, [arg]); typ_level=generic};
      cs_arg = type_unit;
      cs_tag = ConstrRegular(0,2);
      cs_mut = Notmutable;
      cs_kind= Constr_constant }

and constr_cons =
  let arg1 = {typ_desc=Tvar(Tnolink); typ_level=generic} in
  let arg2 = {typ_desc=Tconstr(constr_type_list, [arg1]); typ_level=generic} in
  builtin "::"
    { cs_res = arg2;
      cs_arg = {typ_desc=Tproduct[arg1; arg2]; typ_level=generic};
      cs_tag = ConstrRegular(1,2);
      cs_mut = Notmutable;
      cs_kind= Constr_superfluous 2}
;;

let constr_none =
  let arg = {typ_desc=Tvar(Tnolink); typ_level=generic} in
  builtin "None"
    { cs_res =
       {typ_desc=Tconstr(constr_type_option, [arg]); typ_level=generic};
      cs_arg = type_unit;
      cs_tag = ConstrRegular(0,2);
      cs_mut = Notmutable;
      cs_kind= Constr_constant }

and constr_some =
  let arg = {typ_desc=Tvar(Tnolink); typ_level=generic} in
  builtin "Some"
    { cs_res =
       {typ_desc=Tconstr(constr_type_option, [arg]); typ_level=generic};
      cs_arg = arg;
      cs_tag = ConstrRegular(1,2);
      cs_mut = Notmutable;
      cs_kind= Constr_regular }
;;

let constr_false =
  builtin "false"
    { cs_res = {typ_desc=Tconstr(constr_type_bool,[]); typ_level=notgeneric};
      cs_arg = type_unit;
      cs_tag = ConstrRegular(0,2);
      cs_mut = Notmutable;
      cs_kind= Constr_constant }

and constr_true =
  builtin "true"
    { cs_res = {typ_desc=Tconstr(constr_type_bool,[]); typ_level=notgeneric};
      cs_arg = type_unit;
      cs_tag = ConstrRegular(1,2);
      cs_mut = Notmutable;
      cs_kind= Constr_constant }
;;

(* Some exceptions that must be known to the compiler *)

let match_failure_tag =
  ConstrExtensible ({qual="builtin"; id="Match_failure"}, 1)
;;

let constr_match_failure =
  builtin "Match_failure"
    { cs_res = {typ_desc=Tconstr(constr_type_exn,[]); typ_level=notgeneric};
      cs_arg = type_product [type_string; type_int; type_int];
      cs_tag = match_failure_tag;
      cs_mut = Notmutable;
      cs_kind = Constr_superfluous 3 }
;;

(* Construction of the "builtin" module *)

let module_builtin = new_module "builtin";;

do_list
  (fun (name,desc) ->
      hashtbl__add module_builtin.mod_types name (builtin name desc))
  ["unit",
   {ty_constr=constr_type_unit; ty_arity=0; ty_desc=Variant_type[constr_void]};
   "exn",
    {ty_constr=constr_type_exn; ty_arity=0; ty_desc=Variant_type []};
   "bool",
    {ty_constr=constr_type_bool; ty_arity=0;
     ty_desc=Variant_type [constr_false; constr_true]};
   "int",
    {ty_constr=constr_type_int; ty_arity=0; ty_desc=Abstract_type};
   "float",
    {ty_constr=constr_type_float; ty_arity=0; ty_desc=Abstract_type};
   "string",
    {ty_constr=constr_type_string; ty_arity=0; ty_desc=Abstract_type};
   "char",
    {ty_constr=constr_type_char; ty_arity=0; ty_desc=Abstract_type};
   "list",
    {ty_constr=constr_type_list; ty_arity=1;
     ty_desc=Variant_type [constr_nil; constr_cons]};
   "vect",
    {ty_constr=constr_type_vect; ty_arity=1; ty_desc=Abstract_type};
   "option",
    {ty_constr=constr_type_option; ty_arity=1;
     ty_desc=Variant_type [constr_none; constr_some]}
   ]
;;
(* The type "stream" is defined in the "stream" module *)

do_list
  (fun desc -> hashtbl__add module_builtin.mod_constrs desc.qualid.id desc)
  [constr_void; constr_nil; constr_cons; constr_none; constr_some;
   constr_true; constr_false;
   constr_match_failure ]
;;

hashtbl__add module_table "builtin" module_builtin
;;

(* clauses.ml : detection of unused match clauses and uncomplete matchings *)

#open "misc";;
#open "const";;
#open "globals";;
#open "location";;
#open "syntax";;
#open "lambda";;
#open "types";;

let make_pat desc ty =
  {p_desc = desc; p_loc = no_location; p_typ = ty};;

let omega = make_pat Zwildpat no_type;;

let rec omegas i =
  if i <= 0 then [] else omega::omegas (i-1)
;;

let simple_match p1 p2 = 
  match p1.p_desc, p2.p_desc with
    Zconstruct0pat(c1),Zconstruct0pat(c2) ->
      c1.info.cs_tag = c2.info.cs_tag
  | Zconstruct1pat(c1,_),Zconstruct1pat(c2,_) ->
      c1.info.cs_tag = c2.info.cs_tag
  | Zconstantpat(c1),Zconstantpat(c2) ->
      c1 = c2
  | Ztuplepat(_),Ztuplepat(_) -> true
  | Zrecordpat(_),Zrecordpat(_) -> true
  | _,(Zwildpat | Zvarpat(_)) -> true
  | _,_ -> false
;;



let record_labels p = labels_of_type p.p_typ
;;

let record_nargs p = list_length (record_labels p)
;;


let set_fields size l =

  let v = make_vect size omega in

  let rec change_rec l = match l with
    (lbl,p)::l ->  v.(lbl.info.lbl_pos) <- p ;  change_rec l 
  | [] -> () in

  change_rec l ; list_of_vect v
;;

let simple_match_args p1 p2 =
  match p2.p_desc with
    Zconstruct1pat(_,arg) -> [arg]
  | Ztuplepat(args)  -> args
  | Zrecordpat(args) ->  set_fields (record_nargs p1) args
  | (Zwildpat | Zvarpat(_)) ->
      begin match p1.p_desc with
        Zconstruct1pat(_,_) ->  [omega]
      | Ztuplepat(args) -> map (fun _ -> omega) args
      | Zrecordpat(args) ->  map (fun _ -> omega) args
      | _ -> []
      end
  | _ -> []
;;

(*
  Computes the discriminating pattern for matching by the first
  column of pss, that is:
     checks for a tuple or a record when q is a variable.
*)

let rec simple_pat q pss = match pss with
  ({p_desc = Zaliaspat(p,_)}::ps)::pss -> simple_pat q ((p::ps)::pss)
| ({p_desc = Zconstraintpat(p,_)}::ps)::pss -> simple_pat q ((p::ps)::pss)
| ({p_desc = Zorpat(p1,p2)}::ps)::pss -> simple_pat q ((p1::ps)::(p2::ps)::pss)
| ({p_desc = (Zwildpat | Zvarpat(_))}::_)::pss -> simple_pat q pss
| (({p_desc = Ztuplepat(args)} as p)::_)::_ ->
    make_pat(Ztuplepat(map (fun _ -> omega) args)) p.p_typ
| (({p_desc = Zrecordpat(args)} as p)::_)::pss ->
    make_pat(Zrecordpat (map (fun lbl -> lbl,omega) (record_labels p))) p.p_typ
| _ -> q
;;

let filter_one q pss =

  let rec filter_rec pss = match pss with
    ({p_desc = Zaliaspat(p,_)}::ps)::pss -> filter_rec ((p::ps)::pss)
  | ({p_desc = Zconstraintpat(p,_)}::ps)::pss -> filter_rec ((p::ps)::pss)
  | ({p_desc = Zorpat(p1,p2)}::ps)::pss ->
      filter_rec ((p1::ps)::(p2::ps)::pss)
  | (p::ps)::pss ->
      if simple_match q p then
        (simple_match_args q p @ ps)::filter_rec pss
      else
        filter_rec pss
  | _ -> [] in

  filter_rec pss
;;


let filter_extra pss =

  let rec filter_rec pss = match pss with
    ({p_desc = Zaliaspat(p,_)}::ps)::pss -> filter_rec ((p::ps)::pss)
  | ({p_desc = Zconstraintpat(p,_)}::ps)::pss -> filter_rec ((p::ps)::pss)
  | ({p_desc = Zorpat(p1,p2)}::ps)::pss ->
      filter_rec ((p1::ps)::(p2::ps)::pss)
  | ({p_desc = (Zwildpat | Zvarpat(_))} :: qs) :: pss -> qs :: filter_rec pss
  | _::pss  -> filter_rec pss
  | [] -> [] in

  filter_rec pss
;;

let filter_all pat0 pss =

  let rec insert q qs env = match env with
    [] -> [q,[simple_match_args q q @ qs]]
  | ((p,pss) as c)::env ->
      if simple_match q p then
        (p,((simple_match_args p q @ qs) :: pss)) :: env
      else
        c::insert q qs env in

  let rec filter_rec env pss = match pss with
    ({p_desc = Zaliaspat(p,_)}::ps)::pss -> filter_rec env ((p::ps)::pss)
  | ({p_desc = Zconstraintpat(p,_)}::ps)::pss ->
      filter_rec env ((p::ps)::pss)
  | ({p_desc = Zorpat(p1,p2)}::ps)::pss ->
      filter_rec env ((p1::ps)::(p2::ps)::pss)
  | ({p_desc = (Zwildpat | Zvarpat(_))}::_)::pss -> filter_rec env pss  
  | (p::ps)::pss ->
      filter_rec (insert p ps env) pss
  | _ -> env

  and filter_omega env pss = match pss with
    ({p_desc = Zaliaspat(p,_)}::ps)::pss -> filter_omega env ((p::ps)::pss)
  | ({p_desc = Zconstraintpat(p,_)}::ps)::pss -> filter_omega env ((p::ps)::pss)
  | ({p_desc = Zorpat(p1,p2)}::ps)::pss ->
      filter_omega env ((p1::ps)::(p2::ps)::pss)
  | ({p_desc = (Zwildpat | Zvarpat(_))}::ps)::pss ->
      filter_omega
        (map
          (fun (q,qss) ->
            q,(simple_match_args q omega @ ps) :: qss)
          env)
        pss
  | _::pss -> filter_omega env pss
  | [] -> env in
        
  filter_omega
    (filter_rec
      (match pat0.p_desc with
        (Zrecordpat(_) | Ztuplepat(_)) -> [pat0,[]]
      | _ -> [])
      pss)
    pss
;;

      
let get_span_of_constr cstr =
  match cstr.info.cs_tag with
    ConstrExtensible _      -> 0       (* Meaningless ... *)
  | ConstrRegular(_,span)   -> span
;;


let full_match env = match env with
  ({p_desc = Zconstruct0pat(c)},_) :: _ ->
    list_length env ==  get_span_of_constr c
| ({p_desc = Zconstruct1pat(c,_)},_) :: _ ->
    list_length env =  get_span_of_constr c
| ({p_desc = Zconstantpat(ACchar(_))},_) :: _ ->
    list_length env == 256
| ({p_desc = Zconstantpat(_)},_) :: _ -> false
| ({p_desc = Ztuplepat(_)},_) :: _ -> true
| ({p_desc = Zrecordpat(_)},_) :: _ -> true
| _ -> fatal_error "full_match"
;;

(*
  Is the last row of pattern matrix pss + qs satisfiable ?
        That is :
  Does there exists at least one value vector, es such that :
   1/ for all ps in pss ps # es (ps and es are not compatible)
   2/ qs <= es                  (es matches qs)
*)

let rec satisfiable pss qs = match pss with
  [] -> true
| _ -> match qs with
    [] -> false
  | {p_desc = Zorpat(q1,q2)}::qs ->
      satisfiable pss (q1::qs) || satisfiable pss (q2::qs)
  | {p_desc = Zaliaspat(q,_)}::qs -> satisfiable pss (q::qs)
  | {p_desc = Zconstraintpat(q,_)}::qs -> satisfiable pss (q::qs)
  | {p_desc = (Zwildpat | Zvarpat(_))}::qs ->
      let q0 = simple_pat omega pss in     
      (match filter_all q0 pss with
(* first column of pss is made of variables only *)
        [] -> satisfiable (filter_extra pss) qs 
      | constrs ->          
          let try_non_omega (p,pss) =
            satisfiable pss (simple_match_args p omega @ qs)  in
          if full_match constrs then
            exists try_non_omega constrs
          else
            satisfiable (filter_extra pss) qs
          ||
            exists try_non_omega constrs)
  | q::qs ->
      let q0 = simple_pat q pss in
      satisfiable
        (filter_one q0 pss)
        (simple_match_args q0 q @ qs)
;;


let rec make_matrix pses = match pses with
  (ps,act)::pses ->
     if has_guard act then
       make_matrix pses
     else
       ps::make_matrix pses
| []           -> []
;;

let rec le_pat p q =
  match p.p_desc, q.p_desc with
    (Zvarpat(_)|Zwildpat),_ -> true
  | Zaliaspat(p,_),_ -> le_pat p q
  | _,Zaliaspat(q,_) -> le_pat p q
  | Zconstraintpat(p,_),_ -> le_pat p q
  | _,Zconstraintpat(q,_) -> le_pat p q
  | Zorpat(p1,p2),_ ->
      le_pat p1 q || le_pat p2 q
  | _,Zorpat(q1,q2) ->
       le_pat p q1 && le_pat p q2
  | Zconstantpat(c1), Zconstantpat(c2) -> c1 = c2
  | Zconstruct0pat(c1), Zconstruct0pat(c2) ->
      c1.info.cs_tag == c2.info.cs_tag
  | Zconstruct1pat(c1,p), Zconstruct1pat(c2,q) ->
      c1.info.cs_tag == c2.info.cs_tag && le_pat p q
  | Ztuplepat(ps), Ztuplepat(qs) -> le_pats ps qs
  | Zrecordpat(l1), Zrecordpat(l2) ->
     let size = record_nargs p in
     le_pats (set_fields size l1) (set_fields size l2)
  | _,_ -> false  

and le_pats ps qs = match ps,qs with
  p::ps,q::qs -> le_pat p q && le_pats ps qs
| _           -> true
;;

let get_mins ps =
  let rec select_rec r ps = match ps with
    []      -> r
  | p::ps ->
      if exists (fun p0 -> le_pats p0 p) ps then
        select_rec r ps
      else
        select_rec (p::r) ps in
  select_rec [] (select_rec [] ps)
;;

let partial_match casel =
  let pss = get_mins (make_matrix casel) in
  match pss with
    []     -> true
  | ps::_  -> satisfiable pss (map (fun _ -> omega) ps)
;;


let extract_loc_from_clause clause = match clause with
  pat :: _ -> pat.p_loc
| _ -> fatal_error "extract_loc_from_clause"
;;

let check_unused casel =
  let prefs =   
    list_it
      (fun (ps,act as clause) r ->
         if has_guard act then ([],clause)::r
         else
           ([],clause)::map (fun (pss,clause) -> ps::pss,clause) r)
      casel [] in
  let rec check_rec l   = match l with
    (pss,((qs,_) as clause)) :: l ->       
       if satisfiable pss qs then
         clause::check_rec l
       else
         begin
           error__unused_cases_warning(extract_loc_from_clause qs);
           check_rec l
         end
   | [] -> [] in
   check_rec prefs
;;
(* The compiler entry points *)

#open "misc";;
#open "interntl";;
#open "lexer";;
#open "parser";;
#open "location";;
#open "syntax";;
#open "modules";;
#open "error";;
#open "typing";;
#open "ty_decl";;
#open "pr_decl";;
#open "ty_intf";;
#open "front";;
#open "back";;
#open "emit_phr";;

(* Parsing functions *)

let parse_phrase parsing_fun lexing_fun lexbuf =
  let rec skip () =
    try
      match lexing_fun lexbuf with
        EOF -> ()
      | SEMISEMI -> ()
      | _ -> skip()
    with lexer__Lexical_error(_,_,_) ->
      skip() in
  let skip_maybe () =
    if parsing__is_current_lookahead EOF
    || parsing__is_current_lookahead SEMISEMI
    then () else skip() in
  try
    parsing_fun lexing_fun lexbuf
  with parsing__Parse_error ->
         let pos1 = lexing__get_lexeme_start lexbuf in
         let pos2 = lexing__get_lexeme_end lexbuf in
         skip_maybe();
         eprintf "%aSyntax error.\n" output_location (Loc(pos1, pos2));
         raise Toplevel
     | lexer__Lexical_error(errcode, pos1, pos2) ->
         let l = Loc(pos1, pos2) in
         begin match errcode with
           lexer__Illegal_character ->
             eprintf "%aIllegal character.\n" output_location l
         | lexer__Unterminated_comment ->
             eprintf "%aComment not terminated.\n" output_location l
         | lexer__Bad_char_constant ->
             eprintf "%aIll-formed character literal.\n"
                             output_location l
         | lexer__Unterminated_string ->
             eprintf "%aString literal not terminated.\n"
                             output_location l
         end;
         skip();
         raise Toplevel
     | Toplevel ->
         skip_maybe();
         raise Toplevel
;;

let parse_impl_phrase = parse_phrase parser__Implementation lexer__main
and parse_intf_phrase = parse_phrase parser__Interface lexer__main
;;

(* Executing directives *)

let do_directive loc = function
    Zdir("open", name) ->
      open_module name
  | Zdir("close", name) ->
      close_module name
  | Zdir("infix", name) ->
      add_infix name
  | Zdir("uninfix", name) ->
      remove_infix name
  | Zdir("directory", dirname) ->
      load_path := dirname :: !load_path
  | Zdir(d, name) ->
      eprintf 
        "%aWarning: unknown directive \"#%s\", ignored.\n"
        output_location loc d;
      flush stderr
;;

(* Warn for unused #open *)

let check_unused_opens () =
  if !typing__warnings then
   hashtbl__do_table
     (fun name used ->
       if not !used && not (mem name !default_used_modules)
       then unused_open_warning name)
     !used_opened_modules
;;

(* Compiling an interface *)

let verbose = ref false;;
  
let compile_intf_phrase phr =
  begin match phr.in_desc with
    Zvaluedecl decl ->
      type_valuedecl phr.in_loc decl; ()
  | Ztypedecl decl ->
      let ty_decl = type_typedecl phr.in_loc decl in
      if !verbose then print_typedecl ty_decl
  | Zexcdecl decl ->
      let ex_decl = type_excdecl phr.in_loc decl in
      if !verbose then print_excdecl ex_decl
  | Zintfdirective dir ->
      do_directive phr.in_loc dir
  end
;;

let compile_interface modname filename =
  let source_name = filename ^ ".mli"
  and intf_name = filename ^ ".zi" in
  let ic = open_in_bin source_name (* See compile_impl *)
  and oc = open_out_bin intf_name in
    try
      start_compiling_interface modname;
      let lexbuf = lexing__create_lexer_channel ic in
      input_name := source_name;
      input_chan := ic;
      input_lexbuf := lexbuf;
      external_types := [];
      while true do
        compile_intf_phrase(parse_intf_phrase lexbuf)
      done
    with End_of_file ->
      close_in ic;
      write_compiled_interface oc;
      close_out oc;
      check_unused_opens()
    | x ->
      close_in ic;
      close_out oc;
      remove_file intf_name;
      raise x
;;

(* Compiling an implementation *)

let compile_impl_phrase outstream phr =
  reset_type_expression_vars();
  begin match phr.im_desc with
    Zexpr expr ->
      let ty = type_expression phr.im_loc expr in
      emit_phrase outstream
                  (expr_is_pure expr)
                  (compile_lambda false (translate_expression expr));
      if !verbose then print_expr ty
  | Zletdef(rec_flag, pat_expr_list) ->
      let env = type_letdef phr.im_loc rec_flag pat_expr_list in
      emit_phrase outstream
         (letdef_is_pure pat_expr_list)
         (if rec_flag then
            compile_lambda true (translate_letdef_rec phr.im_loc pat_expr_list)
          else
            compile_lambda false (translate_letdef phr.im_loc pat_expr_list));
      if !verbose then print_valdef env
  | Ztypedef decl ->
      let ty_decl = type_typedecl phr.im_loc decl in
      if !verbose then print_typedecl ty_decl
  | Zexcdef decl ->
      let ex_decl = type_excdecl phr.im_loc decl in
      if !verbose then print_excdecl ex_decl
  | Zimpldirective dir ->
      do_directive phr.im_loc dir
  end
;;

let compile_impl modname filename suffix =
  let source_name = filename ^ suffix
  and obj_name = filename ^ ".zo" in
  let ic = open_in_bin source_name
  (* The source file must be opened in binary mode, so that the absolute
     seeks in print_location work. The lexer ignores both \n and \r,
     so this is OK on the Mac and on the PC. *)
  and oc = open_out_bin obj_name in
  let lexbuf = lexing__create_lexer_channel ic in
    input_name := source_name;
    input_chan := ic;
    input_lexbuf := lexbuf;
    start_emit_phrase oc;
    try
      while true do
        compile_impl_phrase oc (parse_impl_phrase lexbuf)
      done
    with End_of_file ->
      end_emit_phrase oc;
      close_in ic;
      close_out oc;
      check_unused_opens()
    | x ->
      close_in ic;
      close_out oc;
      remove_file obj_name;
      raise x
;;

let write_extended_intf = ref false;;

let compile_implementation modname filename suffix =
  external_types := [];
  if file_exists (filename ^ ".mli") then begin
    try
      let intfname =
        try
          find_in_path (modname ^ ".zi")
        with Cannot_find_file _ ->
          eprintf
            "Cannot find file %s.zi. Please compile %s.mli first.\n"
            modname filename;
          raise Toplevel in
      let intf = read_module modname intfname in
      start_compiling_implementation modname intf;
      enter_interface_definitions intf;
      compile_impl modname filename suffix;
      check_interface intf;
      if !write_extended_intf then begin
        let ext_intf_name = filename ^ ".zix" in
        let oc = open_out_bin ext_intf_name in
        try
          write_compiled_interface oc;
          close_out oc
        with x ->
          close_out oc;
          remove_file (ext_intf_name);
          raise x
      end;
      kill_module modname
    with x ->
      remove_file (filename ^ ".zo");
      raise x
  end else begin
    let intf_name = filename ^ ".zi" in
    let oc = open_out_bin intf_name in
    try
      start_compiling_interface modname;
      compile_impl modname filename suffix;
      check_nongen_values();
      write_compiled_interface oc;
      close_out oc
    with x ->
      close_out oc;
      remove_file intf_name;
      raise x
  end
;;
(* Constants *)

#open "misc";;

type qualified_ident =
  { qual: string;
    id: string }
;;

type constr_tag =
    ConstrExtensible of qualified_ident * int (* name of constructor & stamp *)
  | ConstrRegular of int * int             (* tag number & number of constrs *)
;;

type atomic_constant =
    ACint of int
  | ACfloat of float
  | ACstring of string
  | ACchar of char

and struct_constant =
    SCatom of atomic_constant
  | SCblock of constr_tag * struct_constant list
;;

let const_unit =
    SCblock(ConstrRegular(0,1), [])
;;

let int_of_atom = function
    ACint i -> i
  | ACchar c -> int_of_char c
  | _ -> fatal_error "int_of_atom"
;;

let int_of_constr_tag = function
    ConstrRegular(i,_) -> i
  | ConstrExtensible _ -> fatal_error "int_of_constr_tag"
;;
(* Emitting phrases *)

#open "instruct";;
#open "lambda";;
#open "buffcode";;
#open "emitcode";;

type compiled_phrase =
  { cph_pos: int;                       (* Position of start of code *)
    cph_len: int;                       (* Length of code *)
    cph_reloc: (reloc__info * int) list;(* What to patch *)
    cph_pure: bool;                     (* Can be omitted or not *)
    cph_events: event list }
;;

let abs_out_position = ref 0
;;
let compiled_phrase_index = ref ([] : compiled_phrase list)
;;

let start_emit_phrase outchan =
  output_binary_int outchan 0;
  abs_out_position := 4;
  compiled_phrase_index := []
;;

let emit_phrase outchan is_pure phr =
  reloc__reset();
  event__reset();
  init_out_code();
  labels__reset_label_table();
  begin match phr with
    { kph_fcts = [] } ->
        emit phr.kph_init
  | { kph_rec = false } ->
        emit [Kbranch 0];
        emit phr.kph_fcts;
        emit [Klabel 0];
        emit phr.kph_init
  | { kph_rec = true } ->
        emit phr.kph_init;
        emit [Kbranch 0];
        emit phr.kph_fcts;
        emit [Klabel 0]
  end;
  output outchan !out_buffer 0 !out_position;
  compiled_phrase_index :=
    { cph_pos = !abs_out_position;
      cph_len = !out_position;
      cph_reloc = reloc__get_info();
      cph_events = event__get_events();
      cph_pure = is_pure } :: !compiled_phrase_index;
  abs_out_position := !abs_out_position + !out_position
;;

let end_emit_phrase outchan =
  output_value outchan !compiled_phrase_index;
  compiled_phrase_index := [];
  seek_out outchan 0;
  output_binary_int outchan !abs_out_position
;;


(* Generation of bytecode for .zo files *)

#open "misc";;
#open "const";;
#open "lambda";;
#open "instruct";;
#open "prim";;
#open "opcodes";;
#open "prim_opc";;
#open "buffcode";;
#open "config";;
#open "labels";;

let out_bool_test tst =
  function PTeq -> out tst
      |    PTnoteq -> out (tst + 1)
      |    PTlt -> out (tst + 2)
      |    PTgt -> out (tst + 3)
      |    PTle -> out (tst + 4)
      |    PTge -> out (tst + 5)
      |    _ -> fatal_error "out_bool_test"
;;

let out_int_const i =
  if i <= (maxint_byte-1)/2 && i >= (minint_byte-1)/2 then begin
    out CONSTBYTE; out (i+i+1)
  end else if i <= (maxint_short-1)/2 && i >= (minint_short-1)/2 then begin
    out CONSTSHORT; out_short (i+i+1)
  end else begin
    out GETGLOBAL; reloc__slot_for_literal(SCatom(ACint i))
  end
;;

let out_tag = function
    ConstrRegular(t,_) ->
      out t
  | ConstrExtensible(name, stamp) ->
      reloc__slot_for_tag name stamp
;;

let out_header (n, tag) =
  out_tag tag;
  out (lshift_left n 2);
  out (lshift_right n 6);
  out (lshift_right n 14)
;;

let rec emit = function
      [] -> ()
    | Kquote(SCatom(ACint i)) :: code ->
        out_int_const i;
        emit code
    | Kquote(SCatom(ACchar c)) :: code ->
        out_int_const (int_of_char c);
        emit code
    | Kquote(SCblock(tag,[])) :: code ->
        begin match tag with
          ConstrRegular(t, _) ->
            if t < 10 then out (ATOM0 + t) else (out ATOM; out t)
        | ConstrExtensible(name, stamp) ->
            out ATOM; reloc__slot_for_tag name stamp
        end;
        emit code
    | Kquote(sc) :: code ->
        out GETGLOBAL;
        reloc__slot_for_literal sc;
        emit code
    | Kget_global qualid :: code ->
        out GETGLOBAL;
        reloc__slot_for_get_global qualid;
        emit code
    | Kset_global qualid :: code ->
        out SETGLOBAL;
        reloc__slot_for_set_global qualid;
        emit code
    | Kaccess n :: code ->
        if n < 6 then out(ACC0 + n) else (out ACCESS; out n);
        emit code
    | Kendlet n :: Kendlet p :: code ->
        emit(Kendlet(n+p) :: code)
    | Kendlet 1 :: code ->
        out ENDLET1; emit code
    | Kendlet n :: code ->
        out ENDLET; out n; emit code
    | Kletrec1 lbl :: code ->
        out LETREC1; out_label lbl; emit code
    | Kmakeblock(tag,n) :: code ->
        if n <= 0 then
          fatal_error "emit : Kmakeblock"
        else if n < 5 then begin
          out (MAKEBLOCK1 + n - 1);
          out_tag tag
        end else begin
          out MAKEBLOCK;
          out_header(n, tag)
        end;
        emit code
    | Klabel lbl :: code ->
        if lbl == Nolabel then fatal_error "emit: undefined label" else
          (define_label lbl; emit code)
    | Kclosure lbl :: code ->
        out CUR; out_label lbl; emit code
    | Kpushtrap lbl :: code ->
        out PUSHTRAP; out_label lbl; emit code
    | Kbranch lbl :: code ->
        out BRANCH; out_label lbl; emit code
    | Kbranchif lbl :: code ->
        out BRANCHIF; out_label lbl; emit code
    | Kbranchifnot lbl :: code ->
        out BRANCHIFNOT; out_label lbl; emit code
    | Kstrictbranchif lbl :: code ->
        out BRANCHIF; out_label lbl; emit code
    | Kstrictbranchifnot lbl :: code ->
        out BRANCHIFNOT; out_label lbl; emit code
    | Kswitch lblvect :: code ->
        out SWITCH;
        out (vect_length lblvect);
        let orig = !out_position in
        do_vect (out_label_with_orig orig) lblvect;
        emit code
    | Ktest(tst,lbl) :: code ->
        begin match tst with
            Peq_test ->
              out BRANCHIFEQ; out_label lbl
          | Pnoteq_test ->
              out BRANCHIFNEQ; out_label lbl
          | Pint_test(PTnoteqimm i) ->
              out PUSH; out PUSH; out_int_const i;
              out EQ; out POPBRANCHIFNOT; out_label lbl
          | Pint_test x ->
              out_bool_test BRANCHIFEQ x; out_label lbl
          | Pfloat_test(PTnoteqimm f) ->
              out PUSH; out PUSH; out GETGLOBAL;
              reloc__slot_for_literal (SCatom(ACfloat f));
              out EQFLOAT; out POPBRANCHIFNOT; out_label lbl
          | Pfloat_test x ->
              out_bool_test EQFLOAT x; out BRANCHIF; out_label lbl
          | Pstring_test(PTnoteqimm s) ->
              out PUSH; out PUSH; out GETGLOBAL;
              reloc__slot_for_literal (SCatom(ACstring s));
              out EQSTRING; out POPBRANCHIFNOT; out_label lbl
          | Pstring_test x ->
              out_bool_test EQSTRING x; out BRANCHIF; out_label lbl
          | Pnoteqtag_test tag ->
              out BRANCHIFNEQTAG; out_tag tag; out_label lbl
        end;
        emit code
    | Kbranchinterval(low, high, lbl_low, lbl_high) :: code ->
        out PUSH; out_int_const low; out PUSH;
        if low != high then out_int_const high;
        out BRANCHINTERVAL;
        out_label lbl_low;
        out_label lbl_high;
        emit code
    | Kprim Pidentity :: code ->
        emit code
    | Kprim p :: code ->
        (match p with
            Pdummy n ->
              out DUMMY; out n
          | Ptest tst ->
              (match tst with
                  Peq_test -> out EQ
                | Pnoteq_test -> out NEQ
                | Pint_test tst -> out_bool_test EQ tst
                | Pfloat_test tst -> out_bool_test EQFLOAT tst
                | Pstring_test tst -> out_bool_test EQSTRING tst
                | _ -> fatal_error "emit : Kprim, Ptest")
          | Pfield n ->
              if n < 4 then out (GETFIELD0 + n) else (out GETFIELD; out n)
          | Psetfield n ->
              if n < 4 then out (SETFIELD0 + n) else (out SETFIELD; out n)
          | Pccall(name, arity) ->
              if arity <= 5 then
                out (C_CALL1 + arity - 1)
              else
                (out C_CALLN; out arity);
              reloc__slot_for_c_prim name
          | Pfloatprim p ->
              out FLOATOP;
              out(opcode_for_float_primitive p)
          | p ->
              out(opcode_for_primitive p));
        emit code
    | Kpush :: Kget_global qualid :: Kapply :: code ->
        out PUSH_GETGLOBAL_APPLY;
        reloc__slot_for_get_global qualid;
        emit code
    | Kpush :: Kget_global qualid :: Ktermapply :: code ->
        out PUSH_GETGLOBAL_APPTERM;
        reloc__slot_for_get_global qualid;
        emit code
    | Kevent ev :: code ->
        ev.ev_pos <- !out_position;
        event__enter ev;
        emit code
    | instr :: code ->
        out(match instr with
           Kreturn -> RETURN
        |  Kgrab -> GRAB
        |  Kpush -> PUSH
        |  Kpushmark -> PUSHMARK
        |  Klet -> LET
        |  Kapply -> APPLY
        |  Ktermapply -> APPTERM
        |  Kpoptrap -> POPTRAP
        |  Kcheck_signals -> CHECK_SIGNALS
        |  _  -> fatal_error "emit: should not happen");
        emit code
;;

