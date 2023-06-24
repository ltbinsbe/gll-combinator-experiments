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
(* The abstract syntax for the language *)

#open "const";;
#open "location";;
#open "globals";;

type type_expression =
  { te_desc: type_expression_desc;
    te_loc: location }
and type_expression_desc =
    Ztypevar of string
  | Ztypearrow of type_expression * type_expression
  | Ztypetuple of type_expression list
  | Ztypeconstr of global_reference * type_expression list
;;

type pattern =
  { p_desc: pattern_desc;
    p_loc: location;
    mutable p_typ: typ }
and pattern_desc =
    Zwildpat
  | Zvarpat of string
  | Zaliaspat of pattern * string
  | Zconstantpat of atomic_constant
  | Ztuplepat of pattern list
  | Zconstruct0pat of constr_desc global
  | Zconstruct1pat of constr_desc global * pattern
  | Zorpat of pattern * pattern
  | Zconstraintpat of pattern * type_expression
  | Zrecordpat of (label_desc global * pattern) list
;;

type expression =
  { e_desc: expression_desc;
    e_loc: location;
    mutable e_typ: typ }
and expression_desc =
    Zident of expr_ident ref
  | Zconstant of struct_constant
  | Ztuple of expression list
  | Zconstruct0 of constr_desc global
  | Zconstruct1 of constr_desc global * expression
  | Zapply of expression * expression list
  | Zlet of bool * (pattern * expression) list * expression
  | Zfunction of (pattern list * expression) list
  | Ztrywith of expression * (pattern * expression) list
  | Zsequence of expression * expression
  | Zcondition of expression * expression * expression
  | Zwhile of expression * expression
  | Zfor of string * expression * expression * bool * expression
  | Zconstraint of expression * type_expression
  | Zvector of expression list
  | Zassign of string * expression
  | Zrecord of (label_desc global * expression) list
  | Zrecord_access of expression * label_desc global
  | Zrecord_update of expression * label_desc global * expression
  | Zstream of stream_component list
  | Zparser of (stream_pattern list * expression) list
  | Zwhen of expression * expression

and expr_ident =
    Zglobal of value_desc global
  | Zlocal of string

and stream_component =
    Zterm of expression
  | Znonterm of expression

and stream_pattern =
    Ztermpat of pattern
  | Znontermpat of expression * pattern
  | Zstreampat of string
;;

type type_decl =
    Zabstract_type
  | Zvariant_type of constr_decl list
  | Zrecord_type of (string * type_expression * mutable_flag) list
  | Zabbrev_type of type_expression

and constr_decl =
    Zconstr0decl of string
  | Zconstr1decl of string * type_expression * mutable_flag
;;

type directiveu =
    Zdir of string * string
;;

type impl_phrase =
  { im_desc: impl_desc;
    im_loc: location }
and impl_desc =
    Zexpr of expression
  | Zletdef of bool * (pattern * expression) list
  | Ztypedef of (string * string list * type_decl) list
  | Zexcdef of constr_decl list
  | Zimpldirective of directiveu
;;

type intf_phrase =
  { in_desc: intf_desc;
    in_loc: location }
and intf_desc =
    Zvaluedecl of (string * type_expression * prim_desc) list
  | Ztypedecl of (string * string list * type_decl) list
  | Zexcdecl of constr_decl list
  | Zintfdirective of directiveu
;;

let rec free_vars_of_pat pat =
  match pat.p_desc with
    Zwildpat -> []
  | Zvarpat v -> [v]
  | Zaliaspat(pat,v) -> v :: free_vars_of_pat pat
  | Zconstantpat _ -> []
  | Ztuplepat patl -> flat_map free_vars_of_pat patl
  | Zconstruct0pat(_) -> []
  | Zconstruct1pat(_, pat) -> free_vars_of_pat pat
  | Zorpat(pat1, pat2) -> free_vars_of_pat pat1 @ free_vars_of_pat pat2
  | Zconstraintpat(pat, _) -> free_vars_of_pat pat
  | Zrecordpat lbl_pat_list ->
      flat_map (fun (lbl,pat) -> free_vars_of_pat pat) lbl_pat_list
;;    

let rec expr_is_pure expr =
  match expr.e_desc with
    Zident _ -> true
  | Zconstant _ -> true
  | Ztuple el -> for_all expr_is_pure el
  | Zconstruct0 cstr -> true
  | Zconstruct1(cstr,arg) -> expr_is_pure arg
  | Zfunction _ -> true
  | Zconstraint(expr, ty) -> expr_is_pure expr
  | Zvector el -> for_all expr_is_pure el
  | Zrecord lbl_expr_list ->
      for_all (fun (lbl,e) -> expr_is_pure e) lbl_expr_list
  | Zparser _ -> true
  | _ -> false
;;

let letdef_is_pure pat_expr_list =
  for_all (fun (pat,expr) -> expr_is_pure expr) pat_expr_list
;;

let single_constructor cstr =
  match cstr.info.cs_tag with
    ConstrRegular(_, span) -> span == 1
  | ConstrExtensible(_,_) -> false
;;

let rec pat_irrefutable pat =
  match pat.p_desc with
    Zwildpat -> true
  | Zvarpat s -> true
  | Zaliaspat(pat, _) -> pat_irrefutable pat
  | Zconstantpat _ -> false
  | Ztuplepat patl -> for_all pat_irrefutable patl
  | Zconstruct0pat cstr -> single_constructor cstr
  | Zconstruct1pat(cstr, pat) -> single_constructor cstr && pat_irrefutable pat
  | Zorpat(pat1, pat2) -> pat_irrefutable pat1 || pat_irrefutable pat2
  | Zconstraintpat(pat, _) -> pat_irrefutable pat
  | Zrecordpat lbl_pat_list ->
      for_all (fun (lbl, pat) -> pat_irrefutable pat) lbl_pat_list
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
(* Various useful stuff *)

exception Zinc of string;;

let fatal_error s = raise (Zinc s);;

exception Toplevel;;

let toplevel = ref false;;

let load_path = ref ([] : string list)
;;

let file_exists filename =
  try
    sys__close(sys__open filename [sys__O_RDONLY] 0); true
  with sys__Sys_error _ ->
    false
;;

exception Cannot_find_file of string;;

let find_in_path filename =
  if file_exists filename then
    filename
  else if filename__is_absolute filename then
    raise(Cannot_find_file filename)
  else
    let rec find = function
      [] ->
        raise(Cannot_find_file filename)
    | a::rest ->
        let b = filename__concat a filename in
          if file_exists b then b else find rest
    in find !load_path
;;

let rollback_buffer = ref ([] : (unit -> unit) list);;

let reset_rollback () = rollback_buffer := [];;

let add_rollback f =
  rollback_buffer := f :: !rollback_buffer
;;

let rec rollback () =
  match !rollback_buffer with
    [] -> ()
  | f::rest -> f (); rollback_buffer := rest; rollback()
;;

let remove_file f =
  try
    sys__remove f
  with sys__Sys_error _ ->
    ()
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

(* typing.ml : type inference *)

#open "misc";;
#open "const";;
#open "globals";;
#open "syntax";;
#open "builtins";;
#open "modules";;
#open "types";;
#open "error";;

(* To convert type expressions to types *)

let type_expr_vars =
  ref ([] : (string * typ) list);;

let reset_type_expression_vars () =
  type_expr_vars := []
;;

let bind_type_expression_vars var_list =
  type_expr_vars := [];
  map
    (fun v ->
      if mem_assoc v !type_expr_vars then
        failwith "bind_type_expression_vars"
      else begin
        let t = new_global_type_var() in
        type_expr_vars := (v, t) :: !type_expr_vars; t
      end)
    var_list
;;

let type_of_type_expression strict_flag typexp =
  let rec type_of typexp =
    match typexp.te_desc with
    Ztypevar v ->
      begin try
        assoc v !type_expr_vars
      with Not_found ->
        if strict_flag then
          unbound_type_var_err v typexp
        else begin
          let t = new_global_type_var() in
          type_expr_vars := (v,t) :: !type_expr_vars; t
        end
      end
  | Ztypearrow(arg1, arg2) ->
      type_arrow(type_of arg1, type_of arg2)
  | Ztypetuple argl ->
      type_product(map type_of argl)
  | Ztypeconstr(cstr_name, args) ->
      let cstr =
        try
          find_type_desc cstr_name
        with Desc_not_found ->
          unbound_type_constr_err cstr_name typexp.te_loc in
      if list_length args != cstr.info.ty_arity then
        type_arity_err cstr args typexp.te_loc
      else
        { typ_desc = Tconstr(cstr.info.ty_constr, map type_of args);
          typ_level = notgeneric }
  in type_of typexp
;;

(* Typing of constants *)

let type_of_atomic_constant = function
    ACint _ -> type_int
  | ACfloat _ -> type_float
  | ACstring _ -> type_string
  | ACchar _ -> type_char
;;

let rec type_of_structured_constant = function
    SCatom ac ->
      type_of_atomic_constant ac
  | SCblock(cstr, args) ->
      fatal_error "type_of_structured_constant" (* to do? *)
;;


(* Enables warnings *)
let warnings = ref false;;

(* Typing of patterns *)

let typing_let = ref false;;

let unify_pat pat expected_ty actual_ty =
  try
    unify (expected_ty, actual_ty)
  with Unify ->
    pat_wrong_type_err pat actual_ty expected_ty
;;

let rec tpat new_env (pat, ty, mut_flag) =
  pat.p_typ <- ty;
  match pat.p_desc with
    Zwildpat ->
      new_env
  | Zvarpat v ->
      if mem_assoc v new_env then
        non_linear_pattern_err pat v
      else begin
        if !warnings && (not !typing_let) && v.[0] >= `A` && v.[0] <= `Z` then
          upper_case_variable_warning pat v;
        (v, (ty, mut_flag)) :: new_env
      end
  | Zaliaspat(pat, v) ->
      if mem_assoc v new_env then
        non_linear_pattern_err pat v
      else
        tpat ((v, (ty, mut_flag)) :: new_env) (pat, ty, mut_flag)
  | Zconstantpat cst ->
      unify_pat pat ty (type_of_atomic_constant cst);
      new_env
  | Ztuplepat(patl) ->
      begin try
        tpat_list new_env patl (filter_product (list_length patl) ty)
      with Unify ->
        pat_wrong_type_err pat ty
          (type_product(new_type_var_list (list_length patl)))
      end
  | Zconstruct0pat(cstr) ->
      begin match cstr.info.cs_kind with
        Constr_constant ->
          unify_pat pat ty (type_instance cstr.info.cs_res);
          new_env
      | _ ->
          non_constant_constr_err cstr pat.p_loc
      end
  | Zconstruct1pat(cstr, arg) ->
      begin match cstr.info.cs_kind with
        Constr_constant ->
          constant_constr_err cstr pat.p_loc
      | _ ->
        let (ty_res, ty_arg) =
          type_pair_instance (cstr.info.cs_res, cstr.info.cs_arg) in
        unify_pat pat ty ty_res;
        tpat new_env (arg, ty_arg, cstr.info.cs_mut)
      end
  | Zorpat(pat1, pat2) ->
      begin match free_vars_of_pat pat with
        [] -> tpat (tpat new_env (pat1, ty, mut_flag)) (pat2, ty, mut_flag)
      | _  -> orpat_should_be_closed_err pat
      end
  | Zconstraintpat(pat, ty_expr) ->
      let ty' = type_of_type_expression false ty_expr in
      let new_env' = tpat new_env (pat, ty', mut_flag) in
        unify_pat pat ty ty';
        new_env'
  | Zrecordpat lbl_pat_list ->
      let rec tpat_lbl new_env = function
        [] -> new_env
      | (lbl,p) :: rest ->
          let (ty_res, ty_arg) =
            type_pair_instance (lbl.info.lbl_res, lbl.info.lbl_arg) in
          unify_pat pat ty ty_res;
          tpat_lbl (tpat new_env (p, ty_arg, lbl.info.lbl_mut)) rest
      in
        tpat_lbl new_env lbl_pat_list

and tpat_list new_env = fun
    [] [] ->
      new_env
  | (pat::patl) (ty::tyl) ->
      tpat_list (tpat new_env (pat, ty, Notmutable)) patl tyl
  | _ _ ->
      fatal_error "type_pattern: arity error"
;;

let type_pattern = tpat []
and type_pattern_list = tpat_list []
;;

(* Check if an expression is non-expansive, that is, the result of its 
   evaluation cannot contain newly created mutable objects. *)

let rec is_nonexpansive expr =
  match expr.e_desc with
    Zident id -> true
  | Zconstant sc -> true
  | Ztuple el -> for_all is_nonexpansive el
  | Zconstruct0 cstr -> true
  | Zconstruct1(cstr, e) -> cstr.info.cs_mut == Notmutable && is_nonexpansive e
  | Zlet(rec_flag, bindings, body) ->
      for_all (fun (pat, expr) -> is_nonexpansive expr) bindings &&
      is_nonexpansive body
  | Zfunction pat_expr_list -> true
  | Ztrywith(body, pat_expr_list) ->
      is_nonexpansive body &&
      for_all (fun (pat, expr) -> is_nonexpansive expr) pat_expr_list
  | Zsequence(e1, e2) -> is_nonexpansive e2
  | Zcondition(cond, ifso, ifnot) ->
      is_nonexpansive ifso && is_nonexpansive ifnot
  | Zconstraint(e, ty) -> is_nonexpansive e
  | Zvector [] -> true
  | Zrecord lbl_expr_list ->
      for_all (fun (lbl, expr) ->
                  lbl.info.lbl_mut == Notmutable && is_nonexpansive expr)
              lbl_expr_list
  | Zrecord_access(e, lbl) -> is_nonexpansive e
  | Zparser pat_expr_list -> true
  | Zwhen(cond, act) -> is_nonexpansive act
  | _ -> false
;;

(* Typing of printf formats *)

let type_format loc fmt =
  let len = string_length fmt in
  let ty_input = new_type_var()
  and ty_result = new_type_var() in
  let rec skip_args j =
    if j >= len then j else
      match nth_char fmt j with
        `0` .. `9` | ` ` | `.` | `-` -> skip_args (succ j)
      | _ -> j in
  let rec scan_format i =
    if i >= len then ty_result else
    match nth_char fmt i with
      `%` ->
        let j = skip_args(succ i) in
        begin match nth_char fmt j with
          `%` ->
            scan_format (succ j)
        | `s` ->
            type_arrow (type_string, scan_format (succ j))
        | `c` ->
            type_arrow (type_char, scan_format (succ j))
        | `d` | `o` | `x` | `X` | `u` ->
            type_arrow (type_int, scan_format (succ j))
        | `f` | `e` | `E` | `g` | `G` ->
            type_arrow (type_float, scan_format (succ j))
        | `b` ->
            type_arrow (type_bool, scan_format (succ j))
        | `a` ->
            let ty_arg = new_type_var() in
            type_arrow (type_arrow (ty_input, type_arrow (ty_arg, ty_result)),
                        type_arrow (ty_arg, scan_format (succ j)))
        | `t` ->
            type_arrow (type_arrow (ty_input, ty_result), scan_format (succ j))
        | c ->
            bad_format_letter loc c
        end
    | _ -> scan_format (succ i) in
  {typ_desc=Tconstr(constr_type_format, [scan_format 0; ty_input; ty_result]);
   typ_level=notgeneric}
;;

(* Typing of expressions *)

let unify_expr expr expected_ty actual_ty =
  try
    unify (expected_ty, actual_ty)
  with Unify ->
    expr_wrong_type_err expr actual_ty expected_ty
;;

let rec type_expr env expr =
  let inferred_ty =
  match expr.e_desc with
    Zident r ->
      begin match !r with
          Zglobal glob_desc ->
            type_instance glob_desc.info.val_typ
        | Zlocal s ->
            try
              let (ty_schema, mut_flag) = assoc s env in
                type_instance ty_schema
            with Not_found ->
              try
                let glob_desc = find_value_desc(GRname s) in
                  r := Zglobal glob_desc;
                  type_instance glob_desc.info.val_typ
              with Desc_not_found ->
                unbound_value_err (GRname s) expr.e_loc
      end
  | Zconstant cst ->
      type_of_structured_constant cst
  | Ztuple(args) ->
      type_product(map (type_expr env) args)
  | Zconstruct0(cstr) ->
      begin match cstr.info.cs_kind with
        Constr_constant ->
          type_instance cstr.info.cs_res
      | _ ->
          let (ty_res, ty_arg) =
            type_pair_instance (cstr.info.cs_res, cstr.info.cs_arg) in
          type_arrow(ty_arg, ty_res)
      end            
  | Zconstruct1(cstr, arg) ->
      begin match cstr.info.cs_kind with
        Constr_constant ->
          constant_constr_err cstr expr.e_loc
      | _ ->            
          let (ty_res, ty_arg) =
            type_pair_instance (cstr.info.cs_res, cstr.info.cs_arg) in
          type_expect env arg ty_arg;
          ty_res
      end
  | Zapply(fct, args) ->
      let ty_fct = type_expr env fct in
      let rec type_args ty_res = function
        [] -> ty_res
      | arg1 :: argl ->
          let (ty1, ty2) =
            try
              filter_arrow ty_res
            with Unify ->
              application_of_non_function_err fct ty_fct in
          type_expect env arg1 ty1;
          type_args ty2 argl in
      type_args ty_fct args
  | Zlet(rec_flag, pat_expr_list, body) ->
      type_expr (type_let_decl env rec_flag pat_expr_list) body
  | Zfunction [] ->
      fatal_error "type_expr: empty matching"
  | Zfunction ((patl1,expr1)::_ as matching) ->
      let ty_args = map (fun pat -> new_type_var()) patl1 in
      let ty_res = new_type_var() in
      let tcase (patl, action) =
        if list_length patl != list_length ty_args then
          ill_shaped_match_err expr;
        type_expect (type_pattern_list patl ty_args @ env) action ty_res in
      do_list tcase matching;
      list_it (fun ty_arg ty_res -> type_arrow(ty_arg, ty_res))
              ty_args ty_res
  | Ztrywith (body, matching) ->
      let ty = type_expr env body in
      do_list
        (fun (pat, expr) ->
          type_expect (type_pattern (pat, type_exn, Notmutable) @ env) expr ty)
        matching;
      ty
  | Zsequence (e1, e2) ->
      type_statement env e1; type_expr env e2
  | Zcondition (cond, ifso, ifnot) ->
      type_expect env cond type_bool;
      if match ifnot.e_desc
         with Zconstruct0 cstr -> cstr == constr_void | _ -> false
      then begin
        type_expect env ifso type_unit;
        type_unit
      end else begin
        let ty = type_expr env ifso in
        type_expect env ifnot ty;
        ty
      end
  | Zwhen (cond, act) ->
      type_expect env cond type_bool;
      type_expr env act
  | Zwhile (cond, body) ->
      type_expect env cond type_bool;
      type_statement env body;
      type_unit
  | Zfor (id, start, stop, up_flag, body) ->
      type_expect env start type_int;
      type_expect env stop type_int;
      type_statement ((id,(type_int,Notmutable)) :: env) body;
      type_unit
  | Zconstraint (e, ty_expr) ->
      let ty' = type_of_type_expression false ty_expr in
      type_expect env e ty';
      ty'
  | Zvector elist ->
      let ty_arg = new_type_var() in
      do_list (fun e -> type_expect env e ty_arg) elist;
      type_vect ty_arg
  | Zassign(id, e) ->
      begin try
        match assoc id env with
          (ty_schema, Notmutable) ->
            not_mutable_err id expr.e_loc
        | (ty_schema, Mutable) ->
            type_expect env e (type_instance ty_schema);
            type_unit
      with Not_found ->
        unbound_value_err (GRname id) expr.e_loc
      end
  | Zrecord lbl_expr_list ->
      let ty = new_type_var() in
      do_list
        (fun (lbl, exp) ->
          let (ty_res, ty_arg) =
            type_pair_instance (lbl.info.lbl_res, lbl.info.lbl_arg) in
          begin try unify (ty, ty_res)
          with Unify -> label_not_belong_err expr lbl ty
          end;
          type_expect env exp ty_arg)
        lbl_expr_list;
      let label = vect_of_list (labels_of_type ty) in
      let defined = make_vect (vect_length label) false in
      do_list (fun (lbl, exp) ->
        let p = lbl.info.lbl_pos in
          if defined.(p)
          then label_multiply_defined_err expr lbl
          else defined.(p) <- true)
        lbl_expr_list;
      for i = 0 to vect_length label - 1 do
        if not defined.(i) then label_undefined_err expr label.(i)
      done;
      ty
  | Zrecord_access (e, lbl) ->
      let (ty_res, ty_arg) =
        type_pair_instance (lbl.info.lbl_res, lbl.info.lbl_arg) in
      type_expect env e ty_res;
      ty_arg      
  | Zrecord_update (e1, lbl, e2) ->
      let (ty_res, ty_arg) =
        type_pair_instance (lbl.info.lbl_res, lbl.info.lbl_arg) in
      if lbl.info.lbl_mut == Notmutable then label_not_mutable_err expr lbl;
      type_expect env e1 ty_res;
      type_expect env e2 ty_arg;
      type_unit
  | Zstream complist ->
      let ty_comp = new_type_var() in
      let ty_res = type_stream ty_comp in
      do_list
        (function Zterm e -> type_expect env e ty_comp
                | Znonterm e -> type_expect env e ty_res)
        complist;
      ty_res
  | Zparser casel ->
      let ty_comp = new_type_var() in
      let ty_stream = type_stream ty_comp in
      let ty_res = new_type_var() in
      let rec type_stream_pat new_env = function
        ([], act) ->
          type_expect (new_env @ env) act ty_res
      | (Ztermpat p :: rest, act) ->
          type_stream_pat (tpat new_env (p, ty_comp, Notmutable)) (rest,act)
      | (Znontermpat(parsexpr, p) :: rest, act) ->
          let ty_parser_result = new_type_var() in
          type_expect (new_env @ env) parsexpr
                      (type_arrow(ty_stream, ty_parser_result));
          type_stream_pat (tpat new_env (p, ty_parser_result, Notmutable))
                          (rest,act)
      | (Zstreampat s :: rest, act) ->
          type_stream_pat ((s, (ty_stream, Notmutable)) :: new_env) (rest,act)
      in
      do_list (type_stream_pat [])  casel;
      type_arrow(ty_stream, ty_res)
  in
    expr.e_typ <- inferred_ty;
    inferred_ty

(* Typing of an expression with an expected type.
   Some constructs are treated specially to provide better error messages. *)

and type_expect env exp expected_ty =
  match exp.e_desc with
    Zconstant(SCatom(ACstring s)) ->
      let actual_ty =
        match (type_repr expected_ty).typ_desc with
          (* Hack for format strings *)
          Tconstr(cstr, _) ->
            if cstr = constr_type_format
            then type_format exp.e_loc s
            else type_string
        | _ ->
            type_string in
      unify_expr exp expected_ty actual_ty
  | Zlet(rec_flag, pat_expr_list, body) ->
      type_expect (type_let_decl env rec_flag pat_expr_list) body expected_ty
  | Zsequence (e1, e2) ->
      type_statement env e1; type_expect env e2 expected_ty
  | Zcondition (cond, ifso, ifnot) ->
      type_expect env cond type_bool;
      type_expect env ifso expected_ty;
      type_expect env ifnot expected_ty
  | Ztuple el ->
      begin try
        do_list2 (type_expect env)
                 el (filter_product (list_length el) expected_ty)
      with Unify ->
        unify_expr exp expected_ty (type_expr env exp)
      end
(* To do: try...with, match...with ? *)
  | _ ->
      unify_expr exp expected_ty (type_expr env exp)
  
(* Typing of "let" definitions *)

and type_let_decl env rec_flag pat_expr_list =
  push_type_level();
  let ty_list =
    map (fun (pat, expr) -> new_type_var()) pat_expr_list in
  typing_let := true;
  let add_env =
    type_pattern_list (map (fun (pat, expr) -> pat) pat_expr_list) ty_list in
  typing_let := false;
  let new_env =
    add_env @ env in
  do_list2
    (fun (pat, exp) ty ->
        type_expect (if rec_flag then new_env else env) exp ty)
    pat_expr_list ty_list;
  pop_type_level();
  let gen_type =
    map2 (fun (pat, expr) ty -> (is_nonexpansive expr, ty))
         pat_expr_list ty_list in
  do_list (fun (gen, ty) -> if not gen then nongen_type ty) gen_type;
  do_list (fun (gen, ty) -> if gen then generalize_type ty) gen_type;
  new_env

(* Typing of statements (expressions whose values are ignored) *)

and type_statement env expr =
  let ty = type_expr env expr in
  match (type_repr ty).typ_desc with
  | Tarrow(_,_) -> partial_apply_warning expr.e_loc
  | Tvar _ -> ()
  | _ ->
      if not (same_base_type ty type_unit) then not_unit_type_warning expr ty
;;
(* Concrete syntax for primitive declarations *)

#open "prim";;
#open "globals";;

let find_primitive arity name =
  try
    ValuePrim(arity, assoc name primitive_names)
  with Not_found ->
    ValuePrim(arity, Pccall(name, arity))
;;
(* Auxiliary functions for parsing *)

#open "const";;
#open "misc";;
#open "globals";;
#open "location";;
#open "syntax";;
#open "modules";;
#open "builtins";;
#open "error";;

let make_expr desc =
  {e_desc = desc; e_loc = get_current_location(); e_typ = no_type}
and make_pat desc =
  {p_desc = desc; p_loc = get_current_location(); p_typ = no_type}
and make_typ desc =
  {te_desc = desc; te_loc = get_current_location()}
and make_impl desc =
  {im_desc = desc; im_loc = get_current_location()}
and make_intf desc =
  {in_desc = desc; in_loc = get_current_location()}
;;

let make_apply = function
    {e_desc = Zconstruct0(cstr1)}, [e2] ->
      make_expr(Zconstruct1(cstr1, e2))
  | e1, el ->
      make_expr(Zapply(e1,el))
;;

let make_unop op ({e_loc=Loc(l1,m1)} as e1) =
  let (Loc(l, m) as loc) = get_current_location() in
    {e_desc = Zapply({e_desc = Zident(ref (Zlocal op));
                      e_loc = Loc(l, l1);
                      e_typ = no_type}, [e1]);
     e_loc = loc; e_typ = no_type}
and make_binop op ({e_loc=Loc(l1,m1)} as e1) ({e_loc=Loc(l2,m2)} as e2) =
  make_expr(Zapply({e_desc = Zident(ref (Zlocal op));
                    e_loc = Loc(m1, l2);
                    e_typ = no_type},
                   [e1;e2]))
and make_ternop op ({e_loc=Loc(l1,m1)} as e1) ({e_loc=Loc(l2,m2)} as e2) e3 =
  make_expr(Zapply({e_desc = Zident(ref (Zlocal op));
                    e_loc = Loc(m1, l2);
                    e_typ = no_type},
                   [e1;e2;e3]))
;;

let make_list el =
  let rec makel res = function
    [] ->
      res
  | e::l ->
      makel (make_expr(Zconstruct1(constr_cons, make_expr(Ztuple [e;res])))) l
  in makel (make_expr(Zconstruct0(constr_nil))) el
;;

let make_unary_minus = fun
    "-"  {e_desc = Zconstant(SCatom(ACint i))} ->
      make_expr(Zconstant(SCatom(ACint(minus i))))
  | "-"  {e_desc = Zconstant(SCatom(ACfloat f))} ->
      make_expr(Zconstant(SCatom(ACfloat(minus_float f))))
  | "-"  e ->
      make_unop "minus" e
  | "-." {e_desc = Zconstant(SCatom(ACfloat f))} ->
      make_expr(Zconstant(SCatom(ACfloat(minus_float f))))
  | "-." e ->
      make_unop "minus_float" e
  | _ _ ->
      fatal_error "make_unary_minus"
;;

let find_constructor gr =
  try
    find_constr_desc gr
  with Desc_not_found ->
    unbound_constr_err gr (get_current_location()) gr
;;

let find_label gr =
  try
    find_label_desc gr
  with Desc_not_found ->
    unbound_label_err gr (get_current_location()) gr
;;

let expr_constr_or_ident = function
    GRname s as gr ->
      begin try
        make_expr(Zconstruct0(find_constr_desc gr))
      with Desc_not_found ->
        make_expr(Zident(ref(Zlocal s)))
      end
  | GRmodname q as gr ->
     try
        make_expr(Zconstruct0(find_constr_desc gr))
      with Desc_not_found ->
        try
          make_expr(Zident(ref(Zglobal(find_value_desc gr))))
        with Desc_not_found ->
          unbound_value_err gr (get_current_location())
;;

let pat_constr_or_var s =
  try
    make_pat(Zconstruct0pat(find_constr_desc (GRname s)))
  with Desc_not_found ->
    make_pat(Zvarpat s)
;;

let rec make_range_pat low high =
  if low > high then
    make_range_pat high low
  else if low == high then
    make_pat(Zconstantpat(ACchar(char_of_int low)))
  else
    make_pat(Zorpat(make_pat(Zconstantpat(ACchar(char_of_int low))),
                    make_range_pat (succ low) high))
;;

let make_recordpat = function
    [] -> make_pat(Zwildpat)
  | l -> make_pat(Zrecordpat l);;

let make_listpat pats =
  let rec makel res = function
    [] ->
      res
  | e::l ->
      makel
       (make_pat(Zconstruct1pat(constr_cons, make_pat(Ztuplepat [e;res]))))
       l
  in
    makel (make_pat(Zconstruct0pat(constr_nil))) pats
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
(* Printing a type expression *)

#open "const";;
#open "globals";;
#open "types";;
#open "modules";;

let output_global sel_fct oc gl =
  if not (can_omit_qualifier sel_fct gl) then begin
    output_string oc gl.qualid.qual;
    output_string oc "__"
  end;
  output_string oc gl.qualid.id
;;

let output_type_constr = 
  (output_global types_of_module: out_channel -> type_desc global -> unit)
and output_value =
  (output_global values_of_module: out_channel -> value_desc global -> unit)
and output_constr =
  (output_global constrs_of_module: out_channel -> constr_desc global -> unit)
and output_label =
  (output_global labels_of_module: out_channel -> label_desc global -> unit)
;;

let int_to_alpha i =
  if i < 26
  then make_string 1 (char_of_int (i+97))
  else make_string 1 (char_of_int ((i mod 26) + 97)) ^ string_of_int (i/26)
;;

let type_vars_counter = ref 0
and type_vars_names = ref ([] : (typ * string) list);;

let reset_type_var_name () =
  type_vars_counter := 0; type_vars_names := [];;

let name_of_type_var sch var =
  try
    assq var !type_vars_names
  with Not_found ->
    let name = int_to_alpha !type_vars_counter in
    let var_name =
      if (not sch) || var.typ_level == generic then name else "_" ^ name in
    incr type_vars_counter;
    type_vars_names := (var, var_name) :: !type_vars_names;
    var_name
;;

let rec output_typ oc sch priority ty =
  let ty = type_repr ty in
  match ty.typ_desc with
    Tvar _ ->
      output_string oc "'";
      output_string oc (name_of_type_var sch ty)
  | Tarrow(ty1, ty2) ->
      if priority >= 1 then output_string oc "(";
      output_typ oc sch 1 ty1;
      output_string oc " -> ";
      output_typ oc sch 0 ty2;
      if priority >= 1 then output_string oc ")"
  | Tproduct(ty_list) ->
      if priority >= 2 then output_string oc "(";
      output_typ_list oc sch 2 " * " ty_list;
      if priority >= 2 then output_string oc ")"
  | Tconstr(cstr, args) ->
      begin match args with
        []    -> ()
      | [ty1] ->
          output_typ oc sch 2 ty1; output_string oc " "
      | tyl ->
          output_string oc "(";
          output_typ_list oc sch 0 ", " tyl;
          output_string oc ") "
      end;
      output_global types_of_module oc cstr

and output_typ_list oc sch priority sep = function
    [] ->
      ()
  | [ty] ->
      output_typ oc sch priority ty
  | ty::rest ->
      output_typ oc sch priority ty;
      output_string oc sep;
      output_typ_list oc sch priority sep rest
;;

let output_type oc ty = output_typ oc false 0 ty;;

let output_one_type oc ty = reset_type_var_name(); output_typ oc false 0 ty;;

let output_schema oc ty = reset_type_var_name(); output_typ oc true 0 ty;;
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
(* The Caml Light compiler. Command-line parsing. *)

#open "config";;
#open "misc";;
#open "modules";;
#open "compiler";;

let anonymous s =
  if filename__check_suffix s ".ml" then
    let filename = filename__chop_suffix s ".ml" in
    compile_implementation (filename__basename filename) filename ".ml"
  else if filename__check_suffix s ".mlt" then (* profiler temp files *)
    let filename = filename__chop_suffix s ".mlt" in
    compile_implementation (filename__basename filename) filename ".mlt"
  else if filename__check_suffix s ".mli" then
    let filename = filename__chop_suffix s ".mli" in
    compile_interface (filename__basename filename) filename
  else
    raise (arg__Bad ("don't know what to do with " ^ s))
and set_stdlib p =
  path_library := p;
  load_path := [!path_library]
and add_include d =
  load_path := d :: !load_path
and open_set set =
  try
    default_used_modules := assoc set default_used_interfaces
  with Not_found ->
    raise (arg__Bad ("unknown module set " ^ set))
and show_version () =
  version__print_banner(); flush std_err
and show_types_flag () =
  compiler__verbose := true
and debug_option () =
  event__record_events := true; compiler__write_extended_intf := true
and set_language lang =
  interntl__language := lang
and warnings_option () =
  typing__warnings := true
;;

let main() =
try
  sys__catch_break true;
  default_used_modules := assoc "cautious" default_used_interfaces;
  load_path := [!path_library];
  arg__parse ["-stdlib", arg__String set_stdlib;
              "-I", arg__String add_include;
              "-include", arg__String add_include;
              "-O", arg__String open_set;
              "-open", arg__String open_set;
              "-v", arg__Unit show_version;
              "-version", arg__Unit show_version;
              "-i", arg__Unit show_types_flag;
              "-g", arg__Unit debug_option;
              "-debug", arg__Unit debug_option;
              "-lang", arg__String set_language;
              "-", arg__String anonymous;
              "-W", arg__Unit warnings_option]
             anonymous;
  exit 0
with Toplevel -> exit 2
   | sys__Break -> exit 2
   | sys__Sys_error msg ->
      interntl__eprintf "Input/output error: %s.\n" msg;
      exit 2
   | Zinc s ->
      interntl__eprintf "Internal error: %s.\nPlease report it.\n" s;
      exit 100
;;

printexc__f main (); exit 0;;
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



(* The intermediate language: extended lambda-calculus in de
    Bruijn's notation *)

#open "const";;
#open "prim";;
#open "globals";;

(* Structure of compilation environments *)

type access_path =
    Path_root
  | Path_son of int * access_path
  | Path_tuple of access_path list
;;

type lambda_variable =
  { var_name: string;
    var_path: access_path;
    var_typ: typ }
;;

type transl_env =
    Tnullenv
  | Treserved of transl_env
  | Tenv of lambda_variable list * transl_env
;; 

(* Debugging events *)

type event_kind =
    Lbefore
  | Lafter of typ
;;

type event =
  { ev_kind : event_kind;
    ev_file: string;
    ev_char: int;
    ev_env: transl_env;
    mutable ev_pos: int }
;;

(* The intermediate language *)

type lambda =
    Lvar of int
  | Lconst of struct_constant
  | Lapply of lambda * lambda list
  | Lfunction of lambda
  | Llet of lambda list * lambda
  | Lletrec of (lambda * int) list * lambda
  | Lprim of primitive * lambda list
  | Lcond of lambda * (atomic_constant * lambda) list
  | Lswitch of int * lambda * (constr_tag * lambda) list
  | Lstaticfail of int
  | Lstatichandle of lambda * lambda
  | Lhandle of lambda * lambda
  | Lifthenelse of lambda * lambda * lambda
  | Lsequence of lambda * lambda
  | Lwhile of lambda * lambda
  | Lfor of lambda * lambda * bool * lambda
  | Lshared of lambda * int ref
  | Levent of event * lambda
;;

let share_lambda l =
  Lshared(l, ref (-1))
;;

(* Guards *)
let rec has_guard = function
    Lifthenelse(l1, l2, Lstaticfail _) -> true
  | Levent(ev, l) -> has_guard l
  | Lshared(l, lbl) -> has_guard l
  | Llet(l1, l2) -> has_guard l2
  | _ -> false;;

let guard_expression l1 l2 npops =  Lifthenelse(l1, l2, Lstaticfail npops);;


(* types.ml : basic operations over types *)

#open "misc";;
#open "const";;
#open "globals";;
#open "modules";;

(* Type constructor equality *)

let same_type_constr cstr1 cstr2 =
  cstr1.info.ty_stamp == cstr2.info.ty_stamp &&
  cstr1.qualid.qual = cstr2.qualid.qual
;;

(* To take the canonical representative of a type.
   We do path compression there. *)

let rec type_repr ty =
  match ty.typ_desc with
    Tvar Tnolink ->
      ty
  | Tvar(Tlinkto t1 as r) ->
      let t2 = type_repr t1 in
        r <- Tlinkto t2; t2
  | _ ->
      ty
;;

(* The current nesting level of lets *)

let current_level = ref 0;;

let reset_type_var () =
  current_level := 0; ()
and push_type_level () =
  incr current_level; ()
and pop_type_level () =
  decr current_level; ()
;;

(* To get fresh type variables *)

let new_type_var () =
  {typ_desc = Tvar Tnolink; typ_level = !current_level}
;;

let rec type_var_list n level =
  if n <= 0
  then []
  else {typ_desc=Tvar Tnolink; typ_level=level} :: type_var_list (pred n) level
;;

let new_type_var_list n =
  type_var_list n !current_level
;;

let new_global_type_var () =
  {typ_desc = Tvar Tnolink; typ_level = 1}
;;

(* To compute the free type variables in a type *)

let free_type_vars level ty =
  let fv = ref [] in
  let rec free_vars ty =
    let ty = type_repr ty in
    match ty.typ_desc with
      Tvar _ ->
        if ty.typ_level >= level then fv := ty :: !fv
  | Tarrow(t1,t2) ->
      free_vars t1; free_vars t2
  | Tproduct(ty_list) ->
      do_list free_vars ty_list
  | Tconstr(c, ty_list) ->
      do_list free_vars ty_list in
  free_vars ty;
  !fv
;;

(* To generalize a type *)

let rec gen_type ty =
  let ty = type_repr ty in
  begin match ty.typ_desc with
    Tvar _ ->
      if ty.typ_level > !current_level then ty.typ_level <- generic
  | Tarrow(t1,t2) ->
      let lvl1 = gen_type t1 in
      let lvl2 = gen_type t2 in
      ty.typ_level <- if lvl1 <= lvl2 then lvl1 else lvl2
  | Tproduct(ty_list) ->
      ty.typ_level <- gen_type_list ty_list
  | Tconstr(c, ty_list) ->
      ty.typ_level <- gen_type_list ty_list
  end;
  ty.typ_level

and gen_type_list = function
    [] ->
      notgeneric
  | ty::rest ->
      let lvl1 = gen_type ty in
      let lvl2 = gen_type_list rest in
      if lvl1 <= lvl2 then lvl1 else lvl2
;;

let generalize_type ty =
  let _ = gen_type ty in ()
;;

(* To lower the level of all generalizable variables of a type,
   making them non-generalisable. *)
   
let rec nongen_type ty =
  let ty = type_repr ty in
  match ty.typ_desc with
    Tvar _ ->
      if ty.typ_level > !current_level then ty.typ_level <- !current_level
  | Tarrow(t1, t2) ->
      nongen_type t1; nongen_type t2
  | Tproduct ty_list ->
      do_list nongen_type ty_list
  | Tconstr(cstr, ty_list) ->
      do_list nongen_type ty_list
;;

(* To take an instance of a type *)

(* Since a generic variable always has the "link" field empty (that is,
   set to Tnolink), we reuse that field to store a pointer to the
   fresh variable which is the instance of the generic variable. *)

let rec copy_type = function
    {typ_desc = Tvar(Tnolink as link); typ_level = level} as ty ->
      if level == generic
      then begin let v = new_type_var() in link <- Tlinkto v; v end
      else ty
  | {typ_desc = Tvar(Tlinkto ty); typ_level = level} ->
      if level == generic
      then ty
      else copy_type ty
  | {typ_desc = Tarrow(t1,t2); typ_level = level} as ty ->
      if level == generic
      then {typ_desc = Tarrow(copy_type t1, copy_type t2);
            typ_level = notgeneric}
      else ty
  | {typ_desc = Tproduct tlist; typ_level = level} as ty ->
      if level == generic
      then {typ_desc = Tproduct(map copy_type tlist);
            typ_level = notgeneric}
      else ty
  | {typ_desc = Tconstr(cstr, ty_list); typ_level = level} as ty ->
      if level == generic
      then {typ_desc = Tconstr(cstr, map copy_type ty_list);
            typ_level = notgeneric}
      else ty
;;

(* When copying is over, we restore the "link" field of generic variables
   to Tnolink. *)

let rec cleanup_type = function
    {typ_desc = Tvar(Tnolink); typ_level = level} as ty ->
      ()
  | {typ_desc = Tvar(Tlinkto ty as link); typ_level = level} ->
      if level == generic
      then begin link <- Tnolink end
      else cleanup_type ty
  | {typ_desc = Tarrow(t1,t2); typ_level = level} as ty ->
      if level == generic
      then (cleanup_type t1; cleanup_type t2)
      else ()
  | {typ_desc = Tproduct(tlist); typ_level = level} as ty ->
      if level == generic
      then do_list cleanup_type tlist
      else ()
  | {typ_desc = Tconstr(cstr, ty_list); typ_level = level} as ty ->
      if level == generic
      then do_list cleanup_type ty_list
      else ()
;;

(* Here are the actual instantiation functions. *)

let type_instance ty =
  let ty' = copy_type ty in
    cleanup_type ty;
    ty'

and type_pair_instance (ty1,ty2) =
  let ty1' = copy_type ty1
  and ty2' = copy_type ty2 in
    cleanup_type ty1;
    cleanup_type ty2;
    (ty1', ty2')
;;

(* Expansion of an abbreviation *)

let bind_variable ty1 ty2 =
  match ty1.typ_desc with
    Tvar(Tnolink as link) -> link <- Tlinkto ty2
  | _ -> fatal_error "bind_variable";;

let expand_abbrev params body args =
  let params' = map copy_type params
  and body' = copy_type body in
  do_list cleanup_type params;
  cleanup_type body;
  do_list2 bind_variable params' args;
  body';;

(* The occur check *)

exception Unify;;

let occur_check level0 v =
  occurs_rec where rec occurs_rec ty =
    match type_repr ty with
      {typ_desc = Tvar _; typ_level = level} as ty' ->
        if level > level0 then level <- level0;
        ty' == v
    | {typ_desc = Tarrow(t1,t2)} ->
        occurs_rec t1 || occurs_rec t2
    | {typ_desc = Tproduct(ty_list)} ->
        exists occurs_rec ty_list
    | {typ_desc = Tconstr(_, ty_list)} ->
        exists occurs_rec ty_list
;;

(* Unification *)

let rec unify (ty1, ty2) =
  if ty1 == ty2 then () else begin
    let ty1 = type_repr ty1
    and ty2 = type_repr ty2 in
      if ty1 == ty2 then () else begin
        match (ty1.typ_desc, ty2.typ_desc) with
          Tvar link1, Tvar link2 ->
            if ty1.typ_level < ty2.typ_level
            then begin
              ty2.typ_level <- ty1.typ_level; link2 <- Tlinkto ty1
            end else begin
              ty1.typ_level <- ty2.typ_level; link1 <- Tlinkto ty2
            end
        | Tvar link1, _ when not (occur_check ty1.typ_level ty1 ty2) ->
            link1 <- Tlinkto ty2
        | _, Tvar link2 when not (occur_check ty2.typ_level ty2 ty1) ->
            link2 <- Tlinkto ty1
        | Tarrow(t1arg, t1res), Tarrow(t2arg, t2res) ->
            unify (t1arg, t2arg);
            unify (t1res, t2res)
        | Tproduct tyl1, Tproduct tyl2 ->
            unify_list (tyl1, tyl2)
        | Tconstr(cstr1, []), Tconstr(cstr2, [])
          when cstr1.info.ty_stamp == cstr2.info.ty_stamp (* inline exp. of *)
             && cstr1.qualid.qual = cstr2.qualid.qual -> (* same_type_constr *)
            ()
        | Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args), _ ->
            unify (expand_abbrev params body args, ty2)
        | _, Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args) ->
            unify (ty1, expand_abbrev params body args)
        | Tconstr(cstr1, tyl1), Tconstr(cstr2, tyl2)
          when cstr1.info.ty_stamp == cstr2.info.ty_stamp (* inline exp. of *)
             && cstr1.qualid.qual = cstr2.qualid.qual -> (* same_type_constr *)
            unify_list (tyl1, tyl2)
        | _, _ ->
            raise Unify
      end
  end

and unify_list = function
    [], [] -> ()
  | ty1::rest1, ty2::rest2 -> unify(ty1,ty2); unify_list(rest1,rest2)
  | _ -> raise Unify
;;

(* Two special cases of unification *)

let rec filter_arrow ty =
  match type_repr ty with
    {typ_desc = Tvar link; typ_level = level} ->
      let ty1 = {typ_desc = Tvar Tnolink; typ_level = level}
      and ty2 = {typ_desc = Tvar Tnolink; typ_level = level} in
        link <- Tlinkto {typ_desc = Tarrow(ty1, ty2); typ_level = notgeneric};
        (ty1, ty2)
  | {typ_desc = Tarrow(ty1, ty2)} ->
      (ty1, ty2)
  | {typ_desc = Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args)} ->
      filter_arrow (expand_abbrev params body args)
  | _ ->
      raise Unify
;;

let rec filter_product arity ty =
  match type_repr ty with
    {typ_desc = Tvar link; typ_level = level} ->
      let tyl = type_var_list arity level in
      link <- Tlinkto {typ_desc = Tproduct tyl; typ_level = notgeneric};
      tyl
  | {typ_desc = Tproduct tyl} ->
      if list_length tyl == arity then tyl else raise Unify
  | {typ_desc = Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args)} ->
      filter_product arity (expand_abbrev params body args)
  | _ ->
      raise Unify
;;

(* Type matching. Instantiates ty1 so that it is equal to ty2, or raises
   Unify if not possible. Type ty2 is unmodified. Since the levels in ty1
   are not properly updated, ty1 must not be generalized afterwards. *)

let rec filter (ty1, ty2) =
  if ty1 == ty2 then () else begin
    let ty1 = type_repr ty1
    and ty2 = type_repr ty2 in
      if ty1 == ty2 then () else begin
        match (ty1.typ_desc, ty2.typ_desc) with
          Tvar link1, Tvar link2 when ty1.typ_level != generic ->
            link1 <- Tlinkto ty2
        | Tvar link1, _ when ty1.typ_level != generic
                           && not(occur_check ty1.typ_level ty1 ty2) ->
            link1 <- Tlinkto ty2
        | Tarrow(t1arg, t1res), Tarrow(t2arg, t2res) ->
            filter (t1arg, t2arg);
            filter (t1res, t2res)
        | Tproduct(t1args), Tproduct(t2args) ->
            filter_list (t1args, t2args)
        | Tconstr(cstr1, []), Tconstr(cstr2, [])
          when same_type_constr cstr1 cstr2 ->
            ()
        | Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args), _ ->
            filter (expand_abbrev params body args, ty2)
        | _, Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args) ->
            filter (ty1, expand_abbrev params body args)
        | Tconstr(cstr1, tyl1), Tconstr(cstr2, tyl2)
          when same_type_constr cstr1 cstr2 ->
            filter_list (tyl1, tyl2)
        | _, _ ->
            raise Unify
      end
  end

and filter_list = function
    [], [] -> ()
  | ty1::rest1, ty2::rest2 ->
      filter(ty1,ty2); filter_list(rest1,rest2)
  | _ ->
      raise Unify
;;

(* Simple equality between base types. *)

let rec same_base_type ty base_ty =
  match ((type_repr ty).typ_desc, (type_repr base_ty).typ_desc) with
    Tconstr({info = {ty_abbr = Tabbrev(params,body)}}, args), _ ->
      same_base_type (expand_abbrev params body args) base_ty
  | _, Tconstr({info = {ty_abbr = Tabbrev(params,body)}}, args) ->
      same_base_type ty (expand_abbrev params body args)
  | Tconstr(cstr1, []), Tconstr(cstr2, []) ->
      same_type_constr cstr1 cstr2
  | _, _ ->
      false
;;

(* Extract the list of labels of a record type. *)

let rec labels_of_type ty =
  match (type_repr ty).typ_desc with
    Tconstr({info = {ty_abbr = Tabbrev(params, body)}}, args) ->
      labels_of_type (expand_abbrev params body args)
  | Tconstr(cstr, _) ->
      begin match (type_descr_of_type_constr cstr).info.ty_desc with
        Record_type lbl_list -> lbl_list
      | _ -> fatal_error "labels_of_type"
      end
  | _ ->
      fatal_error "labels_of_type"
;;

(* Check whether a type constructor is a recursive abbrev *)

exception Recursive_abbrev;;

let check_recursive_abbrev cstr =
  match cstr.info.ty_abbr with
    Tnotabbrev -> ()
  | Tabbrev(params, body) ->
      let rec check_abbrev seen ty =
        match (type_repr ty).typ_desc with
          Tvar _ -> ()
        | Tarrow(t1, t2) -> check_abbrev seen t1; check_abbrev seen t2
        | Tproduct tlist -> do_list (check_abbrev seen) tlist
        | Tconstr(c, tlist) ->
            if memq c seen then
              raise Recursive_abbrev
            else begin
              do_list (check_abbrev seen) tlist;
              begin match c.info.ty_abbr with
                Tnotabbrev -> ()
              | Tabbrev(params, body) -> check_abbrev (c :: seen) body
              end
            end
      in check_abbrev [cstr] body
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
(* The type of primitives *)

#open "const";;

type primitive =
    Pidentity
  | Pget_global of qualified_ident
  | Pset_global of qualified_ident
  | Pdummy of int
  | Pupdate
  | Ptest of bool_test
  | Pmakeblock of constr_tag
  | Ptag_of
  | Pfield of int
  | Psetfield of int
  | Pccall of string * int
  | Praise
  | Pnot | Psequand | Psequor
  | Pnegint | Psuccint | Ppredint
  | Paddint | Psubint | Pmulint | Pdivint | Pmodint
  | Pandint | Porint | Pxorint
  | Pshiftleftint | Pshiftrightintsigned | Pshiftrightintunsigned
  | Pincr | Pdecr
  | Pintoffloat
  | Pfloatprim of float_primitive
  | Pstringlength | Pgetstringchar | Psetstringchar
  | Pmakevector | Pvectlength | Pgetvectitem | Psetvectitem

and float_primitive =
    Pfloatofint
  | Pnegfloat | Paddfloat | Psubfloat | Pmulfloat | Pdivfloat

and bool_test =
    Peq_test
  | Pnoteq_test
  | Pint_test of int prim_test
  | Pfloat_test of float prim_test
  | Pstring_test of string prim_test
  | Pnoteqtag_test of constr_tag

and 'a prim_test =
    PTeq
  | PTnoteq
  | PTnoteqimm of 'a
  | PTlt
  | PTle
  | PTgt
  | PTge
;;
(* Typing toplevel phrases *)

#open "const";;
#open "globals";;
#open "builtins";;
#open "syntax";;
#open "modules";;
#open "types";;
#open "error";;
#open "typing";;

let enter_new_variant is_extensible loc (ty_constr, ty_res, constrs) =
  let nbr_constrs =
    list_length constrs in
  let rec make_constrs constr_idx = function
    [] -> []
  | Zconstr0decl constr_name :: rest ->
      let constr_tag =
        if is_extensible then
          ConstrExtensible({qual=compiled_module_name(); id=constr_name},
                           new_exc_stamp())
        else
          ConstrRegular(constr_idx, nbr_constrs) in
      let constr_glob =
        defined_global constr_name
          { cs_res = ty_res;
            cs_arg = type_unit;
            cs_mut = Notmutable;
            cs_tag = constr_tag;
            cs_kind = Constr_constant }
      in
        add_constr constr_glob;
        constr_glob :: make_constrs (succ constr_idx) rest
  | Zconstr1decl(constr_name, arg, mut_flag) :: rest ->
      let ty_arg =
        type_of_type_expression true arg
      and constr_tag =
        if is_extensible then
          ConstrExtensible({qual=compiled_module_name(); id=constr_name},
                           new_exc_stamp())
        else
          ConstrRegular(constr_idx, nbr_constrs) in
      let kind =
        match type_repr ty_arg with
          {typ_desc = Tproduct tylist} ->
            begin match mut_flag with
              Notmutable -> Constr_superfluous (list_length tylist)
            | Mutable    -> Constr_regular
            end
        | _ ->
            Constr_regular in
      let constr_glob =
        defined_global constr_name
          { cs_res = ty_res;
            cs_arg = ty_arg;
            cs_mut = mut_flag;
            cs_tag = constr_tag;
            cs_kind = kind }
      in
        add_constr constr_glob;
        constr_glob :: make_constrs (succ constr_idx) rest
  in
    let constr_descs = make_constrs 0 constrs in
      pop_type_level();
      generalize_type ty_res;
      do_list
        (fun cstr -> generalize_type cstr.info.cs_arg)
        constr_descs;
      Variant_type constr_descs
;;

let enter_new_record loc (ty_constr, ty_res, labels) =
  let rec make_labels i = function
    [] -> []
  | (name, typexp, mut_flag) :: rest ->
      let ty_arg = type_of_type_expression true typexp in
      let lbl_glob =
        defined_global name
          { lbl_res = ty_res; lbl_arg = ty_arg;
            lbl_mut = mut_flag; lbl_pos = i }
      in
        add_label lbl_glob;
        lbl_glob :: make_labels (succ i) rest in
  let label_descs = make_labels 0 labels in
    pop_type_level();
    generalize_type ty_res;
    do_list
      (function lbl -> generalize_type lbl.info.lbl_arg)
      label_descs;
    Record_type label_descs
;;
    
let enter_new_abbrev (ty_constr, ty_params, body) =
  let ty_body = type_of_type_expression true body in
    pop_type_level();
    generalize_type ty_body;
    do_list generalize_type ty_params;
    ty_constr.info.ty_abbr <- Tabbrev(ty_params, ty_body);
    Abbrev_type(ty_params, ty_body)
;;

let enter_new_type (ty_name, params, def) =
  let ty_constr =
    defined_global ty_name
      { ty_stamp = new_type_stamp();
        ty_abbr = Tnotabbrev } in
  let ty_desc =
    defined_global ty_name
      { ty_constr = ty_constr;
        ty_arity = list_length params;
        ty_desc  = Abstract_type } in
  add_type ty_desc;
  (ty_desc, params, def)
;;

type external_type =
  { et_descr: type_desc global;
    et_manifest: bool;
    mutable et_defined: bool };;

let external_types =
  ref ([] : (string * external_type) list);;

let define_new_type loc (ty_desc, params, def) =
  push_type_level();
  let ty_params =
    try
      bind_type_expression_vars params
    with Failure "bind_type_expression_vars" ->
      duplicate_param_in_type_decl_err loc in
  let ty_res =
    { typ_desc = Tconstr(ty_desc.info.ty_constr, ty_params);
      typ_level = notgeneric} in
  let type_comp =
    match def with
      Zabstract_type ->
        pop_type_level(); Abstract_type
    | Zvariant_type constrs ->
        enter_new_variant false loc (ty_desc.info.ty_constr, ty_res, constrs)
    | Zrecord_type labels ->
        enter_new_record loc (ty_desc.info.ty_constr, ty_res, labels)
    | Zabbrev_type body ->
        enter_new_abbrev (ty_desc.info.ty_constr, ty_params, body) in
  ty_desc.info.ty_desc <- type_comp;
  begin try
    let extdef = assoc ty_desc.qualid.id !external_types in
    if extdef.et_manifest || extdef.et_defined then
      illegal_type_redefinition loc extdef.et_descr;
    if extdef.et_descr.info.ty_arity <> ty_desc.info.ty_arity then
      type_decl_arity_err loc extdef.et_descr ty_desc;
    extdef.et_defined <- true;
    let extconstr = extdef.et_descr.info.ty_constr
    and intconstr = ty_desc.info.ty_constr in
    intconstr.info.ty_stamp <- extconstr.info.ty_stamp;
    extconstr.info.ty_abbr  <- intconstr.info.ty_abbr
  with Not_found ->
    ()
  end;
  (ty_res, type_comp)
;;

(* Check if an abbreviation is recursive *)

let check_recursive_abbrev loc (ty, params, def) =
  try
    check_recursive_abbrev ty.info.ty_constr
  with Recursive_abbrev ->
    recursive_abbrev_err loc ty
;;

let type_typedecl loc decl =
  let newdecl = map enter_new_type decl in
  let res = map (define_new_type loc) newdecl in
  do_list (check_recursive_abbrev loc) newdecl;
  res
;;

let type_excdecl loc decl =
  push_type_level();
  reset_type_expression_vars ();
  enter_new_variant true loc (constr_type_exn, type_exn, decl)
;;

let type_valuedecl loc decl =
  let enter_val (name, typexp, prim) =
    push_type_level();
    reset_type_expression_vars ();
    let ty = type_of_type_expression false typexp in
      pop_type_level();
      generalize_type ty;
      add_value (defined_global name { val_typ = ty; val_prim = prim })
  in
    do_list enter_val decl
;;

let type_letdef loc rec_flag pat_expr_list =
  push_type_level();
  let ty_list =
    map (fun (pat, expr) -> new_type_var()) pat_expr_list in
  typing_let := true;
  let env =
    type_pattern_list (map (fun (pat, expr) -> pat) pat_expr_list) ty_list in
  typing_let := false;
  let enter_val =
    do_list
      (fun (name,(ty,mut_flag)) ->
        add_value (defined_global name {val_typ=ty; val_prim=ValueNotPrim})) in
  if rec_flag then enter_val env;
  do_list2
    (fun (pat, exp) ty -> type_expect [] exp ty)
    pat_expr_list ty_list;
  pop_type_level();
  let gen_type =
    map2 (fun (pat, expr) ty -> (is_nonexpansive expr, ty))
         pat_expr_list ty_list in
  do_list (fun (gen, ty) -> if not gen then nongen_type ty) gen_type;
  do_list (fun (gen, ty) -> if gen then generalize_type ty) gen_type;
  if not rec_flag then enter_val env;
  env
;;
  
let type_expression loc expr =
  push_type_level();
  let ty =
    type_expr [] expr in
  pop_type_level();
  if is_nonexpansive expr then generalize_type ty;
  ty
;;
(* Opcodes for the simple primitives. *)

#open "misc";;
#open "prim";;
#open "opcodes";;

let opcode_for_primitive = function
    Pupdate -> UPDATE
  | Praise -> RAISE
  | Pnot -> BOOLNOT
  | Ptag_of -> TAGOF
  | Pnegint -> NEGINT
  | Psuccint -> SUCCINT
  | Ppredint -> PREDINT
  | Paddint -> ADDINT
  | Psubint -> SUBINT
  | Pmulint -> MULINT
  | Pdivint -> DIVINT
  | Pmodint -> MODINT
  | Pandint -> ANDINT
  | Porint -> ORINT
  | Pxorint -> XORINT
  | Pshiftleftint -> SHIFTLEFTINT
  | Pshiftrightintsigned -> SHIFTRIGHTINTSIGNED
  | Pshiftrightintunsigned -> SHIFTRIGHTINTUNSIGNED
  | Pincr -> INCR
  | Pdecr -> DECR
  | Pintoffloat -> INTOFFLOAT
  | Pstringlength -> STRINGLENGTH
  | Pgetstringchar -> GETSTRINGCHAR
  | Psetstringchar -> SETSTRINGCHAR
  | Pmakevector -> MAKEVECTOR
  | Pvectlength -> VECTLENGTH
  | Pgetvectitem -> GETVECTITEM
  | Psetvectitem -> SETVECTITEM
  | _ -> fatal_error "opcode_for_primitive"
;;

let opcode_for_float_primitive = function
    Pfloatofint -> FLOATOFINT
  | Pnegfloat -> NEGFLOAT
  | Paddfloat -> ADDFLOAT
  | Psubfloat -> SUBFLOAT
  | Pmulfloat -> MULFLOAT
  | Pdivfloat -> DIVFLOAT
;;
(* To print the things defined by an implementation *)

#open "misc";;
#open "const";;
#open "globals";;
#open "pr_type";;
#open "printf";;

let print_expr ty =
  printf "(* - : %a *)\n" output_one_type ty;
  flush std_out
;;

let print_valdef env =
  do_list
    (fun (name, (typ, mut_flag)) ->
       printf "value %s : %a;;\n" name output_schema typ)
    env;
  flush std_out
;;

let print_constr_decl cstr =
  match cstr.info.cs_kind with
    Constr_constant ->
      printf "%s\n" cstr.qualid.id
  | _ ->
      printf "%s of %s%a\n"
             cstr.qualid.id
             (match cstr.info.cs_mut with Mutable -> "mutable " | _ -> "")
             output_type cstr.info.cs_arg
;;

let print_label_decl lbl =
  printf "%s%s : %a\n"
         (match lbl.info.lbl_mut with Mutable -> "mutable " | _ -> "")
         lbl.qualid.id output_type lbl.info.lbl_arg
;;

let print_one_typedecl (ty_res, ty_comp) =
  output_one_type stdout ty_res;
  begin match ty_comp with
    Variant_type(cstr1::cstrl) ->
      print_string " = \n  | "; print_constr_decl cstr1;
      do_list (fun cstr -> print_string "  | "; print_constr_decl cstr) cstrl
  | Record_type(lbl1::lbll) ->
      print_string " = \n  { "; print_label_decl lbl1;
      do_list (fun lbl -> print_string "  ; "; print_label_decl lbl) lbll;
      print_string "  }\n"
  | Abbrev_type(_, ty_body) ->
      printf " == %a\n" output_type ty_body
  | Abstract_type ->
      print_string "\n"
  | _ ->
      fatal_error "print_typedecl"
  end
;;

let print_typedecl = function
    [] -> fatal_error "print_typedecl"
  | dcl1::dcll ->
      print_string "type "; print_one_typedecl dcl1;
      do_list (fun dcl -> print_string " and "; print_one_typedecl dcl) dcll;
      print_string ";;\n"; flush std_out
;;

let print_excdecl = function
    Variant_type cstrl ->
      do_list
        (fun cstr ->
          reset_type_var_name();
          print_string "exception ";
          print_constr_decl cstr)
        cstrl;
      print_string ";;\n"; flush std_out
  | _ ->
      fatal_error "print_excdecl"
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

(* Consistency check between an interface and an implementation *)

#open "const";;
#open "globals";;
#open "modules";;
#open "types";;
#open "error";;
#open "ty_decl";;

(* Create the initial environment for compiling an implementation
   when an explicit interface exists. *)

let enter_interface_definitions intf =
  external_types := [];
  hashtbl__do_table
    (fun name ty_desc ->
      let manifest =
        match ty_desc.info.ty_desc with
          Abstract_type -> false
        | _ -> add_type ty_desc; true in
      external_types :=
        (ty_desc.qualid.id,
         {et_descr = ty_desc; et_manifest = manifest; et_defined = false})
        :: !external_types)
    (types_of_module intf);
  hashtbl__do_table
    (fun name val_desc ->
      match val_desc.info.val_prim with
        ValuePrim(_,_) -> add_value val_desc
      |       _        -> ())
    (values_of_module intf);
  hashtbl__do_table
    (fun name constr_desc -> add_constr constr_desc)
    (constrs_of_module intf);
  hashtbl__do_table
    (fun name label_desc -> add_label label_desc)
    (labels_of_module intf)
;;

(* Check that an implementation matches an explicit interface *)

let check_value_match val_decl =
  let val_impl =
    try
      hashtbl__find (values_of_module !defined_module)
                    (little_name_of_global val_decl)
    with Not_found ->
      undefined_value_err val_decl in
  let nongen_vars = free_type_vars notgeneric val_impl.info.val_typ in
  begin try
    filter (type_instance val_impl.info.val_typ, val_decl.info.val_typ)
  with Unify ->
    type_mismatch_err val_decl val_impl
  end;
  if exists (fun ty -> free_type_vars generic ty != []) nongen_vars then
    cannot_generalize_err val_impl
;;

let check_interface intf =
  hashtbl__do_table
    (fun name val_desc ->
      match val_desc.info.val_prim with
        ValueNotPrim -> check_value_match val_desc
      |      _       -> ())
    (values_of_module intf)
;;

(* Check that an implementation without interface does not export values
   with non-generalizable types. *)

let check_nongen_values () =
  hashtbl__do_table
    (fun name val_impl ->
      if free_type_vars notgeneric val_impl.info.val_typ != [] then
        cannot_generalize_err val_impl)
    (values_of_module !defined_module)
;;
(* streams.ml: translation of streams *)

#open "const";;
#open "syntax";;
#open "prim";;
#open "lambda";;
#open "matching";;
#open "tr_env";;

(* The following constants must be kept in sync with the definition
   of type stream in file ../lib/stream.ml *)

let sempty_tag = ConstrRegular(0,5)
and scons_tag  = ConstrRegular(1,5)
and sapp_tag   = ConstrRegular(2,5)
and sfunc_tag  = ConstrRegular(3,5)
;;

(* The following constant must be kept in sync with STREAM_PARSE_FAILURE
   in file ../runtime/fail.h *)

let parse_failure_tag = 10
;;

(* Translation of stream expressions *)

let translate_stream translate_expr env stream_comp_list =
  let rec transl_stream env = function
    [] ->
      Lconst(SCblock(sempty_tag, []))
   | [Znonterm e] ->
      Lprim(Pmakeblock sfunc_tag,
            [Lfunction(translate_expr (Treserved env) e); Lconst(const_unit)])
  | component :: rest ->
      let tag =
        match component with Zterm _ -> scons_tag | Znonterm _ -> sapp_tag in
      let e =
        match component with Zterm e -> e | Znonterm e -> e in
      Lprim(Pmakeblock sfunc_tag,
        [Lfunction(Lprim(Pmakeblock tag,
                         [translate_expr (Treserved env) e;
                          transl_stream (Treserved env) rest]));
         Lconst(const_unit)]) in
  transl_stream env stream_comp_list
;;

(* Translation of stream parsers *)

let stream_oper name =
  Lprim(Pget_global {qual="stream"; id=name}, [])
;;

let stream_raise name tag =
  Lprim(Praise,
        [Lconst(SCblock(ConstrExtensible({qual="stream"; id=name}, tag), []))])
;;

let raise_parse_failure = stream_raise "Parse_failure" 1
and raise_parse_error = stream_raise "Parse_error" 2
;;

let catch_parse_failure l =
  Lhandle(l, Lifthenelse(Lprim(Ptest Peq_test,
                               [Lprim(Ptag_of, [Lvar 0]);
                                Lconst(SCatom(ACint parse_failure_tag))]),
                         Lstaticfail 0,
                         Lprim(Praise, [Lvar 0])))
;;

let rec divide_term_parsing = function
    (Ztermpat pat :: spatl, act) :: rest ->
      let (pat_case_list, parsing) = divide_term_parsing rest in
        (pat, (spatl, act)) :: pat_case_list, parsing
  | parsing ->
        ([], parsing)
;;

let access_stream (* env *) =
  translate_access "%stream" (* env *)
;;

let translate_parser translate_expr loc init_env case_list stream_type =

  let rec transl_inner env (patl, act) =
    match patl with
      [] ->
        translate_expr env act
    | Ztermpat pat :: rest ->
        let (new_env, add_lets, _) = add_pat_to_env env pat in
          Llet([Lapply(stream_oper "stream_require", [access_stream env])],
               translate_matching raise_parse_error
                 [[pat],
                  add_lets(Lsequence(Lapply(stream_oper "stream_junk",
                                                  [access_stream new_env]),
                                     transl_inner new_env (rest,act)))])
    | Znontermpat(parsexpr, pat) :: rest ->
        let (new_env, add_lets, _) = add_pat_to_env env pat in
          Llet([Lapply(stream_oper "parser_require",
                       [translate_expr env parsexpr; access_stream env])],
               translate_matching raise_parse_error
                 [[pat], add_lets(transl_inner new_env (rest,act))])
    | Zstreampat id :: rest ->
        Llet([access_stream env],
             transl_inner (Tenv([var_root id stream_type], env)) (rest,act)) in

  let rec transl_top env parsing =
    match parsing with
      [] ->
        raise_parse_failure
    | ([], act) :: _ ->
        translate_expr env act
    | (Ztermpat _ :: _, _) :: _ ->
        let translate_line (pat, case) =
          let (new_env, add_lets, _) = add_pat_to_env env pat in
            ([pat],
             add_lets(Lsequence(Lapply(stream_oper "stream_junk",
                                                  [access_stream new_env]),
                                transl_inner new_env case))) in
        begin match divide_term_parsing parsing with
          (pat_case_list, []) ->
            Llet([Lapply(stream_oper "stream_peek", [access_stream env])],
                 translate_matching raise_parse_failure
                   (map translate_line pat_case_list))
        | (pat_case_list, rest) ->
            Lstatichandle(
              Llet(
                [catch_parse_failure(Lapply(stream_oper "stream_peek",
                                        [access_stream env]))],
                translate_matching (Lstaticfail 0)
                   (map translate_line pat_case_list)),
              transl_top (Treserved env) rest)
        end
    | (Znontermpat(parsexpr, pat) :: spatl, act) :: [] ->
        let (new_env, add_lets, _) = add_pat_to_env env pat in
          Llet([Lapply(translate_expr env parsexpr, [access_stream env])],
               translate_matching raise_parse_failure
                 [[pat], add_lets(transl_inner new_env (spatl,act))])
    | (Znontermpat(parsexpr, pat) :: spatl, act) :: rest ->
        let (new_env, add_lets, _) = add_pat_to_env env pat in
          Lstatichandle(
            Llet(
              [catch_parse_failure(Lapply(translate_expr env parsexpr,
                                      [access_stream env]))],
              translate_matching (Lstaticfail 0)
                [[pat], add_lets(transl_inner new_env (spatl,act))]),
            transl_top (Treserved env) rest)
    | (Zstreampat id :: spatl, act) :: _ ->
        Llet([access_stream env],
             transl_inner (Tenv([var_root id stream_type], env)) (spatl, act))
  in
    Lfunction(transl_top (Tenv([var_root "%stream" stream_type], init_env))
                         case_list)
;;
(* Relocation information *)

#open "const";;
#open "buffcode";;

type info =
    Reloc_literal of struct_constant    (* structured constant *)
  | Reloc_getglobal of qualified_ident  (* reference to a global *)
  | Reloc_setglobal of qualified_ident  (* definition of a global *)
  | Reloc_tag of qualified_ident * int  (* exception tag *)
  | Reloc_primitive of string           (* C primitive number *)
;;

let reloc_info = ref ([] : (info * int) list);;

let reset () =
  reloc_info := []
;;

let enter info =
  reloc_info := (info, !out_position) :: !reloc_info
;;

let slot_for_literal sc =
  enter (Reloc_literal sc);
  out_short 0
and slot_for_get_global id =
  enter (Reloc_getglobal id);
  out_short 0
and slot_for_set_global id =
  enter (Reloc_setglobal id);
  out_short 0
and slot_for_tag id stamp =
  enter (Reloc_tag(id, stamp));
  out 0
and slot_for_c_prim name =
  enter (Reloc_primitive name);
  out_short 0
;;

let get_info () =
  let res = !reloc_info in reloc_info := []; rev res
;;
(* tr_env.ml: handling of the translation environment. *)

#open "misc";;
#open "const";;
#open "syntax";;
#open "lambda";;
#open "prim";;
#open "error";;
#open "globals";;

let translate_path root =
  let rec transl = function
      Path_root -> root
    | Path_son(n, p) -> Lprim(Pfield n, [transl p])
    | Path_tuple pl -> Lprim(Pmakeblock(ConstrRegular(0,1)), map transl pl)
  in transl
;;

let rec find_var name = function
    [] -> raise Not_found
  | var::remainder ->
      if var.var_name = name then var else find_var name remainder
;;

let rec translate_access s env =
  let rec transl i = function
    Tnullenv      -> fatal_error "translate_env"
  | Treserved env -> transl (i+1) env
  | Tenv(l, env)  ->
      try
        let var = find_var s l in translate_path (Lvar i) var.var_path
      with Not_found ->
        transl (i+1) env
  in transl 0 env
;;

let translate_update s env newval =
  let rec transl i = function
    Tnullenv      -> fatal_error "translate_update"
  | Treserved env -> transl (i+1) env
  | Tenv(l, env)  ->
      try
        let var = find_var s l in
        match var.var_path with
          Path_root -> transl (i+1) env
            (* We have two occurrences of s in the environment:
               one is let-bound (path = Path_root) and is the value
               at the time of the matching,
               the other is a non-trivial access path in the data structure.
               The latter is the one that should be modified, so we skip the
               former. *)
        | Path_son(start,rest) ->
            Lprim(Psetfield start, [translate_path (Lvar i) rest; newval])
        | Path_tuple pl ->
            fatal_error "translate_update"
      with Not_found ->
        transl (i+1) env
  in transl 0 env
;;

let rec pat_is_named pat =
  match pat.p_desc with
    Zvarpat s -> true
  | Zaliaspat(pat, s) -> true
  | Zconstraintpat(pat, _) -> pat_is_named pat
  | _ -> false
;;

let tuple_path nfields path =
  let rec list_of_fields i =
    if i >= nfields then [] else Path_son(i, path) :: list_of_fields (succ i)
  in
    Path_tuple(list_of_fields 0)
;;

let rec paths_of_pat path pat =
  match pat.p_desc with
    Zvarpat s ->
      [{var_name = s; var_path = path; var_typ = pat.p_typ}]
  | Zaliaspat(pat,s) ->
      {var_name = s; var_path = path; var_typ = pat.p_typ} ::
      paths_of_pat path pat
  | Ztuplepat(patlist) ->
      let rec paths_of_patlist i = function
        [] -> []
      | p::pl ->
          paths_of_pat (Path_son(i,path)) p @ paths_of_patlist (i+1) pl in
      paths_of_patlist 0 patlist
  | Zconstruct0pat(cstr) ->
      []
  | Zconstruct1pat(cstr, p) ->
      begin match cstr.info.cs_kind with
        Constr_superfluous n ->
          paths_of_pat (if pat_is_named p then tuple_path n path else path) p
      | _ ->
          paths_of_pat (Path_son(0, path)) p
      end
  | Zconstraintpat(pat,_) ->
      paths_of_pat path pat
  | Zrecordpat lbl_pat_list ->
      let rec paths_of_lbl_pat_list = function
        [] -> []
      | (lbl,p)::pl ->
          paths_of_pat (Path_son(lbl.info.lbl_pos,path)) p @
          paths_of_lbl_pat_list pl in
      paths_of_lbl_pat_list lbl_pat_list
  | _ -> []
;;

let rec mutable_vars_of_pat mut pat =
  match pat.p_desc with
    Zvarpat v ->
      if mut
      then [{var_name = v; var_typ = pat.p_typ; var_path = Path_root}]
      else []
  | Zaliaspat(pat,v) ->
      let l = mutable_vars_of_pat mut pat in
      if mut
      then {var_name = v; var_typ = pat.p_typ; var_path = Path_root} :: l
      else l
  | Zconstraintpat(pat, _) -> mutable_vars_of_pat mut pat
  | Ztuplepat patl -> flat_map (mutable_vars_of_pat mut) patl
  | Zconstruct1pat(cstr,pat) ->
      let mut' =
        match cstr.info.cs_mut with
          Mutable -> true
        | Notmutable -> mut in
      mutable_vars_of_pat mut' pat
  | Zrecordpat lbl_pat_list ->
      flat_map
        (fun (lbl,pat) ->
          let mut' =
            match lbl.info.lbl_mut with
              Mutable -> true
            | Notmutable -> mut in
          mutable_vars_of_pat mut' pat)
        lbl_pat_list
  | _ -> []                             (* Zwildpat or Zconstpat or Zorpat *)
;;

let rec add_lets_to_env varlist env =
  match varlist with
    [] -> env
  | var::rest -> add_lets_to_env rest (Tenv([var], env))
;;      

let add_lets_to_expr varlist env expr =
  let rec add env = function
      [] -> []
    | var::rest ->
        translate_access var.var_name env :: add (Treserved env) rest in
  match add env varlist with
    [] -> expr
  | el -> Llet(el, expr)
;;

let add_pat_to_env env pat =
  let env' = Tenv(paths_of_pat Path_root pat, env) in
  let mut_vars = mutable_vars_of_pat false pat in
  (add_lets_to_env mut_vars env',
   add_lets_to_expr mut_vars env',
   list_length mut_vars)
;;

let add_pat_list_to_env env patl =
  let env' =
    it_list (fun env pat -> Tenv(paths_of_pat Path_root pat, env)) env patl in
  let mut_vars =
    flat_map (mutable_vars_of_pat false) patl in
  (add_lets_to_env mut_vars env',
   add_lets_to_expr mut_vars env',
   list_length mut_vars)
;;

(* The parameter of a "for" loop is let-bound with index 0.
   The variable with index 1 is the end-of-loop value.
   The variable with index 2 is the reference itself. *)

let add_for_parameter_to_env env id =
  let var =
    {var_name = id;
     var_path = Path_root;
     var_typ = builtins__type_int} in
  Tenv([var], Treserved(Treserved(env)))
;;

(* Used for expansion of stream expressions *)

let var_root id typ =
  { var_name = id; var_path = Path_root; var_typ = typ }
;;

(* For let rec: check that the pattern is a variable *)

let add_let_rec_to_env env pat_expr_list =
  let rec add env (pat, expr) =
    match pat.p_desc with
      Zvarpat v ->
        Tenv([{var_name = v; var_path = Path_root; var_typ = pat.p_typ}], env)
    | Zconstraintpat(p, ty) ->
        add env (p, expr)
    | _ ->
        illegal_letrec_pat pat.p_loc in
  it_list add env pat_expr_list
;;
    
let env_for_toplevel_let patl =
  it_list (fun env pat -> Tenv(paths_of_pat Path_root pat, env)) Tnullenv patl
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
(*  match.ml : expansion of pattern-matching as a cascade of tests. *)

#open "misc";;
#open "const";;
#open "globals";;
#open "builtins";;
#open "error";;
#open "syntax";;
#open "location";;
#open "lambda";;
#open "prim";;
#open "clauses";;

(*  See Peyton-Jones, The Implementation of functional programming
    languages, chapter 5. *)

(* A pattern-matching is represented as a disjunction of conjunctions:

      pat & pat & ... & pat  ->  action
    | pat & pat & ... & pat  ->  action
    | ...
    | pat & pat & ... & pat  ->  action

      exp   exp   ...   exp

  A pattern "pat" applies to (i.e. must match) the expression below it. *)

type pattern_matching =
  Matching of (pattern list * lambda) list * lambda list
;;

(* Simple pattern manipulations *)

let make_path n = function
    (path::pathl) ->
      let rec make i =
        if i >= n then pathl else Lprim(Pfield i, [path]) :: make (i+1) in
      make 0
  | _ ->
      fatal_error "make_path"
;;

let add_to_match (Matching(casel,pathl)) cas =
  Matching(cas :: casel, pathl)

and make_constant_match = fun
    (path :: pathl) cas -> Matching([cas], pathl)
  | _ _ -> fatal_error "make_constant_match"

and make_tuple_match arity pathl =
  Matching([], make_path arity pathl)

and make_construct_match = fun
  cstr (path :: pathl as pathl0) cas ->
  (match cstr.info.cs_kind with
    Constr_constant ->
      Matching([cas], pathl)
  | Constr_superfluous n ->
      Matching([cas], pathl0)
  | _ ->
      Matching([cas], Lprim(Pfield 0, [path]) :: pathl))
| _ _ _ -> fatal_error "make_construct_match"
;;

(* Auxiliaries for factoring common tests *)

let add_to_division make_match divlist key cas =
  try
    let matchref = assoc key divlist in
      matchref := add_to_match !matchref cas; divlist
    with Not_found ->
      (key, ref (make_match cas)) :: divlist
;;

(* To skip type constraints and aliases, and flatten "or" patterns. *)

let rec simpl_casel = function
    ({p_desc = Zaliaspat(pat,v)} :: patl, action) :: rest ->
      simpl_casel ((pat::patl, action) :: rest)
  | ({p_desc = Zconstraintpat(pat,ty)} :: patl, action) :: rest ->
      simpl_casel ((pat::patl, action) :: rest)
  | ({p_desc = Zorpat(pat1, pat2)} :: patl, action) :: rest ->
      simpl_casel ((pat1::patl, action) :: (pat2::patl, action) :: rest)
  | casel ->
      casel
;;

(* Factoring pattern-matchings. *)

let divide_constant_matching (Matching(casel, pathl)) =
  divide_rec casel where rec divide_rec casel =
    match simpl_casel casel with
      ({p_desc = Zconstantpat(cst)} :: patl, action) :: rest ->
        let (constant, others) = divide_rec rest in
          add_to_division
            (make_constant_match pathl) constant cst (patl, action),
          others
    | casel ->
        [], Matching(casel, pathl)
;;

let wildcard_pat =
  {p_desc = Zwildpat; p_loc = no_location; p_typ = no_type};;

let divide_tuple_matching arity (Matching(casel, pathl)) =
  divide_rec casel where rec divide_rec casel =
    match simpl_casel casel with
      ({p_desc = Ztuplepat(args)} :: patl, action) :: rest ->
        add_to_match (divide_rec rest) (args @ patl, action)
    | ({p_desc = (Zwildpat | Zvarpat _)} :: patl, action) :: rest ->
        let rec make_pats i =
          if i >= arity then [] else wildcard_pat :: make_pats (i+1) in
        add_to_match (divide_rec rest) (make_pats 0 @ patl, action)
    | [] ->
        make_tuple_match arity pathl
    | _ ->
        fatal_error "divide_tuple_matching"
;;

let divide_construct_matching (Matching(casel, pathl)) =
  divide_rec casel where rec divide_rec casel =
    match simpl_casel casel with
      ({p_desc = Zconstruct0pat(c)} :: patl, action) :: rest ->
        let (constrs, others) =
          divide_rec rest in
        add_to_division
          (make_construct_match c pathl) constrs c.info.cs_tag (patl, action),
        others
    | ({p_desc = Zconstruct1pat(c,arg)} :: patl, action) :: rest ->
        let patl' =
          match c.info.cs_kind with
            Constr_constant -> patl
          |          _      -> arg :: patl in
        let (constrs, others) =
          divide_rec rest in
        add_to_division
          (make_construct_match c pathl) constrs c.info.cs_tag (patl', action),
        others
    | casel ->
        [], Matching(casel, pathl)
;;

let divide_var_matching = function
  Matching(casel, (_ :: endpathl as pathl)) ->
    let rec divide_rec casel =
      match simpl_casel casel with
        ({p_desc = (Zwildpat | Zvarpat _)} :: patl, action) :: rest ->
          let vars, others = divide_rec rest in
            add_to_match vars (patl, action),
            others
      | casel ->
          Matching([], endpathl), Matching(casel, pathl)
    in divide_rec casel
| _ -> fatal_error "divide_var_matching"
;;

let divide_record_matching ty_record (Matching(casel, pathl)) =
  let labels = types__labels_of_type ty_record in
  let num_labels = list_length labels in
  let rec divide_rec = function
      ({p_desc = Zaliaspat(pat,v)} :: patl, action) :: rest ->
        divide_rec ((pat::patl, action) :: rest)
    | ({p_desc = Zconstraintpat(pat,ty)} :: patl, action) :: rest ->
        divide_rec ((pat::patl, action) :: rest)
    | ({p_desc = Zorpat(pat1, pat2)} :: patl, action) :: rest ->
        divide_rec ((pat1::patl, action) :: (pat2::patl, action) :: rest)
    | ({p_desc = Zrecordpat pat_expr_list} :: patl, action) :: rest ->
        divide_rec_cont pat_expr_list patl action rest
    | ({p_desc = (Zwildpat | Zvarpat _)} :: patl, action) :: rest ->
        divide_rec_cont [] patl action rest
    | [] ->
        Matching([], make_path num_labels pathl)
    | _ ->
        fatal_error "divide_record_matching"
  and divide_rec_cont pat_expr_list patl action rest =
    let v = make_vect num_labels wildcard_pat in
    do_list (fun (lbl, pat) -> v.(lbl.info.lbl_pos) <- pat) pat_expr_list;
    add_to_match (divide_rec rest) (list_of_vect v @ patl, action)
  in
    divide_rec casel
;;

(* Utilities on pattern-matchings *)

let length_of_matching (Matching(casel,_)) = list_length casel
;;

let upper_left_pattern =
  let rec strip = function
      {p_desc = Zaliaspat(pat,_)} -> strip pat
    | {p_desc = Zconstraintpat(pat,_)} -> strip pat
    | {p_desc = Zorpat(pat1,pat2)} -> strip pat1
    | pat -> pat in
  function Matching((pat::_, _) :: _, _) -> strip pat
      |                _                 -> fatal_error "upper_left_pattern"
;;

let get_span_of_constr cstr =
  match cstr.info.cs_tag with
    ConstrExtensible _      -> 0       (* Meaningless ... *)
  | ConstrRegular(tag,span) -> span
;;

let get_span_of_matching matching =
  match upper_left_pattern matching with
      {p_desc = Zconstruct0pat(c)}   -> get_span_of_constr c
    | {p_desc = Zconstruct1pat(c, _)} -> get_span_of_constr c
    | _ -> fatal_error "get_span_of_matching"
;;

(* The tri-state booleans. *)

type tristate_logic = False | Maybe | True;;

let tristate_or = function
    (True, _)     -> True
  | (_, True)     -> True
  | (False,False) -> False
  |      _        -> Maybe
;;

(* The main compilation function.
   Input: a pattern-matching,
   Output: a lambda term and a "total" flag.
   The "total" flag is approximated: it is true if the matching is
   guaranteed to be total, and false otherwise. *)

let rec conquer_matching =
  let rec conquer_divided_matching = function
    [] ->
      ([], true)
  | (key, matchref) :: rest ->
      let (lambda1, total1) = conquer_matching !matchref
      and (list2,   total2) = conquer_divided_matching rest in
        ((key, lambda1) :: list2, total1 && total2)
  in function
    Matching([], _) ->
      (Lstaticfail 0, false)
   | Matching(([], action) :: rest, pathl) ->
      if has_guard action then begin
        let (lambda2, total2) = conquer_matching (Matching (rest, pathl)) in
        (Lstatichandle(action, lambda2), total2)
      end else
        (action, true)
  | Matching(_, (path :: _)) as matching ->
      begin match upper_left_pattern matching with
        {p_desc = (Zwildpat | Zvarpat _)} ->
          let vars, rest = divide_var_matching matching in
          let lambda1, total1 = conquer_matching vars
          and lambda2, total2 = conquer_matching rest in
            if total1
            then (lambda1, true)
            else (Lstatichandle(lambda1, lambda2), total2)
      | {p_desc = Ztuplepat patl} ->
          conquer_matching (divide_tuple_matching (list_length patl) matching)
      | {p_desc = (Zconstruct0pat(_) | Zconstruct1pat(_,_))} ->
          let constrs, vars = divide_construct_matching matching in
          let (switchlst, total1) = conquer_divided_matching constrs
          and (lambda,    total2) = conquer_matching vars in
          let span = get_span_of_matching matching
          and num_cstr = list_length constrs in
            if num_cstr = span && total1 then
              (Lswitch(span, path, switchlst), true)
            else
              (Lstatichandle(Lswitch(span, path, switchlst), lambda),
               total2)
      | {p_desc = Zconstantpat _} ->
          let constants, vars = divide_constant_matching matching in
            let condlist1, _ = conquer_divided_matching constants
            and lambda2, total2 = conquer_matching vars in
              (Lstatichandle(Lcond(path, condlist1), lambda2), total2)
      | {p_desc = Zrecordpat _; p_typ = ty} ->
          conquer_matching (divide_record_matching ty matching)
      | _ ->
          fatal_error "conquer_matching 2"
      end
  | _ -> fatal_error "conquer_matching 1"
;;

(* Auxiliaries to build the initial matching *)

let make_initial_matching = function
    [] ->
      fatal_error "make_initial_matching: empty"
  | (patl, _) :: _ as casel ->
      let rec make_path n =
        if n <= 0 then [] else Lvar(n-1) :: make_path(n-1)
      in
        Matching(casel, make_path(list_length patl))
;;

let partial_fun (Loc(start, stop)) =
  Lprim(Praise,
    [Lconst(SCblock(match_failure_tag,
      [SCatom(ACstring !input_name);SCatom(ACint start);SCatom(ACint stop)]))])
;;

(* The entry points *)

let translate_matching_check_failure loc casel =
  let casel' =
    map (fun (patl, act) -> (patl, share_lambda act)) (check_unused casel) in
  if partial_match casel then not_exhaustive_warning loc;
  let (lambda, total) = conquer_matching (make_initial_matching casel') in
  if total then lambda else Lstatichandle(lambda, partial_fun loc)
;;

let translate_matching failure_code casel =
  let casel' =
    map (fun (patl, act) -> (patl, share_lambda act)) (check_unused casel) in
  let (lambda, total) = conquer_matching (make_initial_matching casel') in
  if total then lambda else Lstatichandle(lambda, failure_code)
;;
(* modules.ml : handling of modules and global symbol tables *)

#open "misc";;
#open "const";;
#open "globals";;

(* Informations associated with module names *)

type module =
  { mod_name: string;                        (* name of the module *)
    mod_values: (string, value_desc global) hashtbl__t;
                                             (* table of values *)
    mod_constrs: (string, constr_desc global) hashtbl__t;
                                             (* table of constructors *)
    mod_labels: (string, label_desc global) hashtbl__t;
                                             (* table of labels *)
    mod_types: (string, type_desc global) hashtbl__t;
                                             (* table of type constructors *)
    mutable mod_type_stamp: int;             (* stamp for type constructors *)
    mutable mod_exc_stamp: int;              (* stamp for exceptions *)
    mutable mod_persistent: bool }
                      (* true if this interface comes from a .zi file *)
;;

let name_of_module    md = md.mod_name
and values_of_module  md = md.mod_values
and constrs_of_module md = md.mod_constrs
and labels_of_module  md = md.mod_labels
and types_of_module   md = md.mod_types
;;

(* The table of module interfaces already loaded in memory *)

let module_table = (hashtbl__new 37 : (string, module) hashtbl__t);;

let new_module nm =
  let md =
    { mod_name = nm;
      mod_values = hashtbl__new 17;
      mod_constrs = hashtbl__new 13;
      mod_labels = hashtbl__new 11;
      mod_types = hashtbl__new 7;
      mod_type_stamp = 0;
      mod_exc_stamp = 0;
      mod_persistent = false }
  in
    hashtbl__add module_table nm md; md
;;

(* To load an interface from a file *)

let read_module basename filename =
  let ic = open_in_bin filename in
  try
    let md = (input_value ic : module) in
    close_in ic;
    md.mod_persistent <- true;
    md
  with End_of_file | Failure _ ->
    close_in ic;
    interntl__eprintf "Corrupted compiled interface file %s.\n\
                       Please recompile %s.mli or %s.ml first.\n"
      filename basename basename;
    raise Toplevel
;;

let use_extended_interfaces = ref false;;

let load_module name =
  try
    let fullname = find_in_path (name ^ ".zi") in
    let extname = fullname ^ "x" in
    read_module name
      (if !use_extended_interfaces && file_exists extname
       then extname else fullname)
  with Cannot_find_file _ ->
    interntl__eprintf "Cannot find the compiled interface file %s.zi.\n" name;
    raise Toplevel
;;

(* To find an interface by its name *)

let find_module filename =
  let modname = filename__basename filename in
  try
    hashtbl__find module_table modname
  with Not_found ->
    let md = load_module filename in
      hashtbl__add module_table modname md; md
;;

(* To remove the in-memory image of an interface *)

let kill_module name =
  hashtbl__remove module_table name
;;

(* The table of all opened modules. Associate to each unqualified name
   the corresponding descriptor from the right opened module. *)

let opened_modules = ref
  { mod_name = "";
    mod_values = hashtbl__new 1;
    mod_constrs = hashtbl__new 1;
    mod_labels = hashtbl__new 1;
    mod_types = hashtbl__new 1;
    mod_type_stamp = 1;
    mod_exc_stamp = 1;
    mod_persistent = false };;
let opened_modules_names = ref ([]: string list);;
let used_opened_modules = ref (hashtbl__new 1: (string, bool ref) hashtbl__t);;

let reset_opened_modules () =
  opened_modules :=
    { mod_name = "";
      mod_values = hashtbl__new 73;
      mod_constrs = hashtbl__new 53;
      mod_labels = hashtbl__new 41;
      mod_types = hashtbl__new 29;
      mod_type_stamp = 0;
      mod_exc_stamp = 0;
      mod_persistent = false };
  opened_modules_names := [];
  used_opened_modules := hashtbl__new 13;;

(* Open a module and add its definitions to the table of opened modules. *)

let add_table t1 t2 =
  hashtbl__do_table_rev (hashtbl__add t2) t1;;

let open_module name =
  let module = find_module name in
  add_table module.mod_values (!opened_modules).mod_values;
  add_table module.mod_constrs (!opened_modules).mod_constrs;
  add_table module.mod_labels (!opened_modules).mod_labels;
  add_table module.mod_types (!opened_modules).mod_types;
  opened_modules_names := name :: !opened_modules_names;
  hashtbl__add !used_opened_modules name (ref false);;

(* Close a module and remove its definitions from the table of opened modules.
   To avoid heavy hashtbl hacking, we just rebuild the table from scratch.
   Inefficient, but #close is not frequently used. *)

let close_module name =
  let other_modules_names = except name !opened_modules_names in
  reset_opened_modules();
  do_list open_module (rev other_modules_names);;

(* The current state of the compiler *)

let default_used_modules = ref ([] : string list);;

let defined_module = ref (new_module "");;

let start_compiling_interface name =
  defined_module := new_module name;
  reset_opened_modules();
  do_list open_module !default_used_modules;;

let start_compiling_implementation name intf =
  start_compiling_interface name;
  !defined_module.mod_type_stamp <- intf.mod_type_stamp;
  !defined_module.mod_exc_stamp  <- intf.mod_exc_stamp;;

let compiled_module_name () =
  !defined_module.mod_name
;;

let defined_global name desc =
  { qualid = { qual=compiled_module_name(); id=name }; info = desc }
;;

let new_type_stamp () =
  let s = succ !defined_module.mod_type_stamp in
  !defined_module.mod_type_stamp <- s; s
;;

let new_exc_stamp () =
  let s = succ !defined_module.mod_exc_stamp in
  !defined_module.mod_exc_stamp <- s; s
;;

(* Additions to the module being compiled *)

let add_global_info sel_fct glob =
  let tbl = sel_fct !defined_module in
    if !toplevel then
      add_rollback (fun () -> hashtbl__remove tbl glob.qualid.id);
    hashtbl__add tbl glob.qualid.id glob
;;

let add_value = add_global_info values_of_module
and add_constr = add_global_info constrs_of_module
and add_label = add_global_info labels_of_module
and add_type = add_global_info types_of_module
;;

(* Find the descriptor for a reference to a global identifier.
   If the identifier is qualified (mod__name), just look into module mod.
   If the identifier is not qualified, look inside the current module,
   then inside the table of opened modules. *)

exception Desc_not_found;;

let find_desc sel_fct = function
    GRmodname q ->
      begin try
        hashtbl__find (sel_fct (find_module q.qual)) q.id
      with Not_found ->
        raise Desc_not_found
      end
  | GRname s ->
      try
        hashtbl__find (sel_fct !defined_module) s
      with Not_found ->
        try
          let res = hashtbl__find (sel_fct !opened_modules) s in
          (* Record the module as actually used *)
          (hashtbl__find !used_opened_modules res.qualid.qual) := true;
          res
        with Not_found ->
          raise Desc_not_found
;;

let find_value_desc = find_desc values_of_module
and find_constr_desc = find_desc constrs_of_module
and find_label_desc = find_desc labels_of_module
and find_type_desc = find_desc types_of_module
;;

let type_descr_of_type_constr cstr =
  let rec select_type_descr = function
    [] -> raise Desc_not_found
  | desc::rest ->
      if desc.info.ty_constr.info.ty_stamp = cstr.info.ty_stamp
      then desc
      else select_type_descr rest in
  select_type_descr
    (hashtbl__find_all
      (types_of_module (find_module cstr.qualid.qual))
      cstr.qualid.id)
;;

(* To write the interface of the module currently compiled *)

let write_compiled_interface oc =
  output_value oc !defined_module
;;

(* To flush all in-core modules coming from .zi files *)

let flush_module_cache () =
  let opened = !opened_modules_names in
  hashtbl__do_table
    (fun name md -> if md.mod_persistent then kill_module name)
    module_table;
  reset_opened_modules();
  do_list open_module (rev opened)
;;

let can_omit_qualifier sel_fct gl =
  try
    let gl' =
      try
        hashtbl__find (sel_fct !defined_module) gl.qualid.id
      with Not_found ->
        hashtbl__find (sel_fct !opened_modules) gl.qualid.id in
    gl.qualid = gl'.qualid
  with Not_found ->
    false
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

