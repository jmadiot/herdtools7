(** Usage:
 cat2coq7 sc.cat > sc.v
 *)

open Printf

let a : int -> unit =
  let n = ref 0 in
  function _ -> if !n = 0 then failwith "" else decr n

(** Coq-encodable expressions + try/with *)

let pprint_op1 : AST.op1 -> string -> string =
  let open AST in
  function
  | Inv -> sprintf "%s^-1"
  | Comp -> sprintf "~%s"
  | ToId -> sprintf "[%s]"
  | Plus -> sprintf "%s^+"
  | Star -> sprintf "%s^*"
  | Opt -> sprintf "%s?"

type t = AST.op2

type op2 = Union | Cons | Seq | Inter | Sub | Cartes | Cast

let pprint_op2 = function
  | Union -> "|"
  | Cons -> "++"
  | Seq -> ";"
  | Inter -> "&"
  | Sub -> "\\"
  | Cartes -> "*"
  | Cast -> ":"

type exp =
  | Var_ of string
  | Cst of string (* a variable introduced by this translation. It
                     cannot be substituted *)
  | App_ of exp * exp
  | Fun_ of string list * exp
  | Let_ of string * exp * exp
  | Fix of string * string list * exp
  | Tup of exp list
  | Op1 of AST.op1 * exp
  | Op2 of op2 * exp * exp
  | Try_ of exp * exp
  | Annot of string * exp

let rec free_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = free_vars in
  function
  | Var_ x -> singleton x
  | Cst x -> singleton x
  | App_ (e1, e2) -> f e1 + f e2
  | Fun_ (xs, e) -> List.fold_right remove xs (f e)
  | Let_ (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun_ (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try_ (e1, e2) -> f e1 + f e2
  | Annot (_, e) -> f e


(** Variables appearing in [try _] *)

let rec tried_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = tried_vars in
  function
  | Var_ _ -> empty
  | Cst _ -> empty
  | App_ (e1, e2) -> f e1 + f e2
  | Fun_ (xs, e) -> List.fold_right remove xs (f e)
  | Let_ (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun_ (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try_ (e1, e2) -> free_vars e1 + f e2
  | Annot (_, e) -> f e


(** Free variables not counting the ones in [try _] *)

let rec used_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = used_vars in
  function
  | Var_ x -> singleton x
  | Cst _ -> empty
  | App_ (e1, e2) -> f e1 + f e2
  | Fun_ (xs, e) -> List.fold_right remove xs (f e)
  | Let_ (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun_ (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try_ (_, e2) -> f e2
  | Annot (_, e) -> f e


(** [fresh x vars] returns a name like [x] not belonging to [vars] *)

let name_like (x : string) : int -> string = function
  | 0 -> x
  | 1 -> x ^ "_"
  | n -> x ^ "_" ^ string_of_int (n - 2)

let first (f : int -> 'a) (filter : 'a -> bool) =
  let rec aux n = if filter (f n) then f n else aux (n + 1) in
  aux 0

let fresh (x : string) (vars : StringSet.t) =
  first (name_like x) (fun y -> not (StringSet.mem y vars))


(** Substitution, used in shadowing elimination *)

let rec subst (sub : exp StringMap.t) : exp -> exp =
  (* We are about to apply the substitution [sub] in an expression
     [body] where [x] is binding e.g. [fun x -> body]. This returns
     [x', body', sub'] to prepare for the substitution -- but it does
     not do the substitution *)
  let abs x body sub =
    let open StringSet in
    let fv_sub = unions (List.map (fun (_, e) -> free_vars e)
                          (StringMap.bindings sub)) in
    if mem x fv_sub then
      (* If [x] appears in the codomain of [sub] we must alpha-convert
         it to a locally fresh [x'] *)
      let x' = fresh x (union fv_sub (free_vars body)) in
      let body' = subst (StringMap.singleton x (Var_ x')) body in
      (x', body', sub)
    else
      (* Otherwise, nothing to do, except removing a possible [x] from
         the domain of [sub] *)
      (x, body, StringMap.remove x sub)
  in
  
  (* Do the same thing for a sequence of variables *)
  let rec abs' xs body sub =
    match xs with
    | [] -> ([], body, sub)
    | x :: xs ->
       let (x', body', sub') = abs x body sub in
       let (xs', body'', sub'') = abs' xs body' sub'
       in (x' :: xs', body'', sub'')
  in
  function
  | Var_ x          -> StringMap.safe_find (Var_ x) x sub
  | Cst s           -> Cst s
  | App_ (e1, e2)   -> App_(subst sub e1, subst sub e2)
  | Fun_ (xs, e)    -> let (xs, e, sub) = abs' xs e sub in
                       Fun_(xs, subst sub e)
  | Let_ (x, e1, e2) -> let e1 = subst sub e1 in (* x not binding in e1 *)
                       let (x, e2, sub) = abs x e2 sub in
                       Let_ (x, e1, subst sub e2)
  | Fix (x, xs, e)  -> let (xxs, e, sub) = abs' (x :: xs) e sub in
                       Fix (List.hd xxs, List.tl xxs, subst sub e)
  | Tup es          -> Tup (List.map (subst sub) es)
  | Op1 (o, e1)     -> Op1 (o, subst sub e1)
  | Op2 (o, e1, e2) -> Op2 (o, subst sub e1, subst sub e2)
  | Try_ (e1, e2)    -> Try_ (subst sub e1, subst sub e2)
  | Annot (s, e)    -> Annot (s, subst sub e)

let subst_with_var (sub : string StringMap.t) : exp -> exp =
  subst (StringMap.map (fun x -> Var_ x) sub)


(** Pretty-printing, with greedy currying *)

let level_op2 = function
  | Union -> 70
  | Cons -> 60
  | Seq -> 55
  | Inter -> 51
  | Sub -> 45
  | Cartes -> 40
  | Cast -> 2

let right_associative = function
  | Union | Cons | Seq | Inter -> true
  | Sub | Cartes | Cast -> false

let rec cascade_op (o : op2) : exp -> exp list =
  function
  | Op2 (o', e1, e2) when o = o' -> e1 :: cascade_op o e2
  | e -> [e]

let rec pprint_exp e =
  let p = pprint_exp in
  let ppar e = match e with
    | Var_ x | Cst x -> x
    | Op1 (AST.ToId, _) -> p e
    | _ -> "(" ^ p e ^ ")"
  in
  let open String in
  match e with
  | Var_ x -> x
  | Cst s -> s
  | App_(App_(e1, e2), e3) -> ppar e1 ^ " " ^ ppar e2 ^ " " ^ ppar e3
  | App_(e1, Tup es) -> ppar e1 ^ " " ^ concat " " (List.map ppar es)
  | App_(e1, e2) -> ppar e1 ^ " " ^ ppar e2
  | Op1 (o, e1) -> pprint_op1 o (ppar e1)
  | Op2 (o, e1, e2) ->
     if right_associative o then
       concat (" " ^ pprint_op2 o ^ " ") (List.map ppar (e1 :: cascade_op o e2))
     else
       sprintf "%s %s %s" (ppar e1) (pprint_op2 o) (ppar e2)
  | Tup l -> "(" ^ (concat ", " (List.map p l)) ^ ")"
  | Fun_(xs, e) -> sprintf "fun %s => %s" (concat " " xs) (p e)
  | Fix (f, xs, body) -> sprintf "fix %s %s := %s" f (concat " " xs) (p body)
  | Let_ (x, e1, e2) -> sprintf "let %s := %s in %s" x (p e1) (p e2)
  | Annot (comment, e) -> sprintf "(*%s*) %s" comment (p e)
  | Try_ (e1, e2) -> sprintf "try %s with %s" (p e1) (p e2)

let rec has_notations e : bool =
  let f = has_notations in
  match e with
  | Var_ _ | Cst _ -> false
  | Op1 (_, _) | Op2 (_, _, _) -> true
  | Fun_(_, e) | Fix (_, _, e) | Annot (_, e) -> f e
  | App_(e1, e2) | Let_ (_, e1, e2) | Try_ (e1, e2) -> f e1 || f e2
  | Tup es -> List.exists f es

let pprint_exp_scope e =
  if has_notations e
  then "(" ^ pprint_exp e ^ ")%cat"
  else pprint_exp e

let print_exp = pprint_exp_scope


(** Instructions, parameterized by a type for possibly-generated names *)

type 'name instr =
  | Def of 'name * string option * exp
  | Axiom of 'name * exp
  | Inductive of (string * 'name * exp) list
  | Withfrom of string * 'name * exp
  | Comment of string

type name = Fresh of string | Normal of string


(** Free and defined variables mentioned in an instruction *)

let free_vars_of_instr (fv: 'a -> string list) : 'a instr -> StringSet.t =
  let open StringSet in
  let (+) xs set = List.fold_right add xs set in
  (* let (+) s = function Normal x -> add x s | Fresh _ -> s in *)
  function
  | Def (x, _, e) -> fv x + free_vars e
  | Axiom (x, e) -> fv x + free_vars e
  | Inductive defs ->
     unions (List.map (fun (x, y, e) -> [x] + (fv y + free_vars e)) defs)
  | Withfrom (x, y, e) -> [x] + (fv y + free_vars e)
  | Comment _ -> empty

let free_vars_of_instrs (fv: 'a -> string list) (l : 'a instr list) =
  StringSet.unions (List.map (free_vars_of_instr fv) l)


(** Type annotations for cases for which Cst fails at inference. This
   is less useful since currying has become the norm *)

let force_type : string -> string option =
  function
  | "toid" -> Some "rln events"
  | _ -> None


(** Defs that are too complex to translate, so we remove them
   and define them in the prelude *)

let remove_defs = 
  ["co_locs"; "cross"; "map"]


(** Defs that are in the prelude but can be shadowed *)
let shadowable =
  [ "empty_pred"; "universal"; "complement"; "union"; "intersection";
    "diff"; "rln_comp"; "rln_mirror"; "cartesian"; "incl"; "id";
    "to_id"; "domain"; "range"; "diagonal"; "acyclic"; "is_empty";
    "irreflexive"; "clos_trans"; "clos_refl_trans"; "clos_refl";
    "empty"; "set"; "rln"; "not"; "total_order"; "linearisations";
    "set_flatten"; "set_map"; "loc"; "classes-loc"; "_";  "emptyset";
    "W"; "R"; "M"; "IW"; "FW"; "B"; "RMW"; "F"; "empty"; "sig" ]

let in_prelude = remove_defs @ shadowable

let fence_sets = [
    ("X86", ["MFENCE"; "SFENCE"; "LFENCE"]);
    ("PPC", ["SYNC"; "LWSYNC"; "EIEIO"; "ISYNC"]);
    ("ARM", ["DMB"; "DMB.ST"; "DSB"; "DSB.ST"; "ISB"]);
    ("MIPS", ["SYNC"]);
    ("AArch64",
     let conds =
       [ ""; ".SY"; ".LD"; ".ST";
         ".ISH"; ".ISHLD"; ".ISHST";
         ".NSH"; ".NSHLD"; ".NSHST";
         ".OSH"; ".OSHLD"; ".OSHST" ]
     in ["ISB"; "ISB.SY"]
        @ List.map ((^) "DMB") conds
        @ List.map ((^) "DSB") conds
    );
  ]

let fence_sets =
  fence_sets
  (* We can detect the architecture or say it Sys.argv instead of just
     adding everything like as below *)
  |> List.map snd |> List.concat
  |> List.sort compare
  |> let rec uniq = function
       | [] -> []
       | [x] -> [x]
       | a :: b :: l when a = b -> uniq (a :: l)
       | a :: b :: l -> a :: uniq (b :: l)
     in uniq

let on_demand =
  let oftype ty = List.map (fun id -> (id, ty)) in
  oftype "set events" fence_sets
  @ oftype "set events" [
        "L"; "A"; "X"; "I"; "UL"; "F"; "E"; "LS"; "LK"; "CON"; "Q"; "T";
        "NoRet"; "fence"; "tag2events"; "RMW";
        "Sc"; "SC";
        "ACQ_REL"; "ACQ"; "REL"; "RLX";
        "AcqRel"; "Acq"; "Rel";
        "Fence.r.r" ; "Fence.r.w" ; "Fence.r.rw" ;
        "Fence.w.r" ; "Fence.w.w" ; "Fence.w.rw" ;
        "Fence.rw.r"; "Fence.rw.w"; "Fence.rw.rw";
        "Fence.tso";
      ]
  @ oftype "rln events"
      ["addr"; "amo"; "dmb.st"; "dsb.st";
       "ctrl"; "data"; "po"; "rf"; "fr";
       "rmw"; "co"; "coi"; "sm"; "int"; "ext";
       "coe"; "fre"; "ppo" ;
       "strong"; "light";
       "cc0"; "ci0"; "ic0"; "ii0"; (* for ppo.cat *)
       "iico_ctrl"; "iico_data";
      ]
  @ oftype "rln events -> rln events" ["noid"; "RR"; "RW"; "WR"; "WW"]
  @ [("generate_orders", "set events -> rln events -> set (rln events)")]

let duplicates (l : 'a list) : 'a list =
  List.filter (fun x -> 1 <> List.length (List.find_all ((=) x) l)) l

let () =
  let f l = let d = duplicates l in if d <> [] then failwith (String.concat ", " d) in
  f (List.map fst on_demand)

let special_cases =
  List.map @@
    function
    (* Next line only for co.v TODO ask Luc *)
    | Def (x, _, App_ ((Var_ ("int" | "ext") as a), (Var_ ("co" | "fr") as b))) ->
       Def (x, None, App_ (App_ (Cst "intersection", a), b))
    | Def (x, _, e) -> Def (x, force_type x, e)
    | instr -> instr


(** Printing instructions *)

let t = ref 0

let pprint_instr (i : string instr) : string list =
  let opt = function None -> "" | Some s -> ": " ^ s ^ " " in
  let indent = String.make !t ' ' in
  match i with
  | Comment "INDENT" -> t := !t + 2; []
  | Comment "DEDENT" -> t := !t - 2; []
  | _ ->
     [indent ^
       match i with
       | Comment s -> sprintf "(* %s *)" s
       | Def (x, ty, Fun_ (xs, e)) ->
          sprintf "Definition %s %s %s:= %s."
            x (String.concat " " xs) (opt ty) (pprint_exp e)
       | Def (x, ty, e) -> sprintf "Definition %s %s:= %s." x (opt ty) (pprint_exp e)
       | Axiom (x, e) -> sprintf "Axiom %s : %s." x (pprint_exp e)
       | Inductive defs ->
          let f (x, cx, e) =
            sprintf "%s : rln _ := %s : incl (%s) %s" x cx (pprint_exp e) x
          in sprintf "Inductive %s."
               (String.concat ("\n" ^ indent ^ "with ")
                  (List.map f defs))
       | Withfrom _ ->
          invalid_arg "withfroms should have been eliminated before"
     ]


(** Translating base operators *)

let exp_of_op1 : AST.op1 -> exp =
  let app (x, y) = App_ (x, y) in
  let open AST in
  function
  | Plus -> app (Cst "clos_trans", Cst "_")
  | Star -> app (Cst "clos_refl_trans", Cst "_")
  | Opt -> app (Cst "clos_refl", Cst "_")
  | Comp -> Cst "complement"
  | Inv -> Cst "rln_mirror"
  | ToId -> Cst "to_id"

let translate_op1 (o : AST.op1) e = App_ (exp_of_op1 o, e)

let translate_op1_keep (o : AST.op1) e =
  Op1 (o, e)

let rec translate_op2 (o : AST.op2) (es : exp list) : exp =
  let app2 x e1 e2 = App_ (App_ (Cst x, e1), e2) in
  match o, es with
  | AST.Union, [] -> Cst "empty"
  | AST.Union, [e] -> e
  | AST.Union, (e :: l) -> app2 "union" e (translate_op2 AST.Union l)
  | AST.Inter, [e1; e2] -> app2 "intersection" e1 e2
  | AST.Diff, [e1; e2] -> app2 "diff" e1 e2
  | AST.Cartesian, [e1; e2] -> app2 "cartesian" e1 e2
  | AST.Add, [e1; e2] -> app2 "add_element" e1 e2
  | AST.Seq, [e] -> e
  | AST.Seq, (e :: l) -> app2 "rln_comp" e (translate_op2 AST.Seq l)
  | AST.Tuple, e -> Tup e
  | ((AST.Inter | AST.Diff | AST.Cartesian | AST.Add),
     ([] | [_] | _ :: _ :: _ :: _)) | (AST.Seq, []) ->
     invalid_arg "op2 (invalid arity)"

let rec translate_op2_keep (o : AST.op2) (es : exp list) : exp =
  match o, es with
  | AST.Union, [] -> Cst "empty"
  | AST.Union, [e] -> e
  | AST.Union, (e :: l) -> Op2 (Union, e, (translate_op2_keep AST.Union l))
  | AST.Inter, [e1; e2] -> Op2 (Inter, e1, e2)
  | AST.Diff, [e1; e2] ->  Op2 (Sub, e1, e2)
  | AST.Cartesian, [e1; e2] -> Op2 (Cartes, e1, e2)
  | AST.Add, [e1; e2] -> Op2 (Cons, e1, e2)
  | AST.Seq, [e] -> e
  | AST.Seq, (e :: l) -> Op2 (Seq, e, translate_op2_keep AST.Seq l)
  | _ -> translate_op2 o es


(** Translating expressions *)

let vars_of_pat : AST.pat -> string list =
  let f = function None -> "_" | Some x -> x in
  function AST.Pvar p -> [f p] | AST.Ptuple ps -> List.map f ps

let rec translate_exp (keepnotations : bool) (e : AST.exp) : exp =
  let f e = translate_exp keepnotations e in
  let invalid_arg s = invalid_arg ("translate_exp: " ^ s) in
  let rec lets e2 = function
    | [] -> e2
    | (x, e1) :: l -> Let_ (x, e1, lets e2 l)
  in
  let nicer_binding = function
    | (_, AST.Pvar None, e1) -> ("_", e1)
    | (_, AST.Pvar (Some x), e1) -> (x, e1)
    | (_, AST.Ptuple _, _) -> invalid_arg "destructuring binding"
  in
  let (op1, op2) =
    if keepnotations
    then (translate_op1_keep, translate_op2_keep)
    else (translate_op1, translate_op2)
  in
  let open AST in
  match e with
  | Konst (_, Empty (SET | RLN)) -> Cst "empty"
  | Konst (_, Universe (SET | RLN)) -> Cst "universal"
  | Tag (_, tag) -> Cst (sprintf "Tag \"%s\"" tag)
  | Var (_, k) -> Var_ k
  | Op1 (_, o, exp) -> op1 o (f exp)
  | Op (_, o, args) -> op2 o (List.map f args)
  | App (_, e1, e2) -> App_ (f e1, f e2)
  | Try (_, e1, e2) -> Try_ (f e1, f e2)
  | Bind (_, bindings, e2) ->
     bindings
     |> List.map nicer_binding
     |> List.map (fun (x, e1) -> (x, f e1))
     |> lets (f e2)
  | BindRec (_, bindings, e2) ->
     (* Warning: completely untested *)
     begin match bindings with
     | [] -> invalid_arg "empty let rec in"
     | _ :: _ :: _ -> invalid_arg "mutual let rec in"
     | [(_, Ptuple _, _)] -> invalid_arg "destructuring in let rec"
     | [(_, Pvar None, _)] -> invalid_arg "nameless let rec"
     | [(_, Pvar (Some name), (Fun (_, pat, body, _, _)))] ->
        Let_ (name, Fix (name, vars_of_pat pat, f body), f e2)
     | [(_, Pvar _, _)] -> invalid_arg "let rec in with no argument"
     end
  | Fun (_, pat, exp, _name, _freevars) ->
     Fun_ (vars_of_pat pat, f exp)
  | ExplicitSet (_, []) -> Op2 (Cast, Cst "empty", App_ (Cst "set", Cst "_"))
  | ExplicitSet (_, [e]) -> App_ (Cst "singleton", f e)
  | ExplicitSet (l, (e :: t)) -> Op2 (Cons, f e, f (ExplicitSet (l, t)))
  | Match _ -> invalid_arg "match not implemented"
  | MatchSet _ -> invalid_arg "matchset not implemented"
  | If _ -> invalid_arg "if"


(** Translate a kind of test into an expression *)
let of_test (t : AST.test) k (e : AST.exp) : exp =
  let e = translate_exp k e in
  let f (t : AST.do_test) = Cst (match t with
    | AST.Acyclic -> "acyclic"
    | AST.Irreflexive -> "irreflexive"
    | AST.TestEmpty -> "is_empty")
  in
  match t with
  | AST.Yes t -> App_ (f t, e)
  | AST.No t -> App_ (Cst "not", (App_ (f t, e)))


(** Converting cat commands instruction by instruction & recursively
   import files *)

let rec translate_instr k (parse_file : string -> AST.ins list) (i : AST.ins)
  : name instr list =
  let invalid_arg s = invalid_arg ("of_instr: " ^ s) in
  let open AST in
  match i with
  | Include (_, filename) ->
     [Comment (sprintf "Import from %s:" filename)]
     @ [Comment "INDENT"]
     @ List.concat (List.map (translate_instr k parse_file) (parse_file filename))
     @ [Comment "DEDENT"]
     @ [Comment (sprintf "End of import from %s" filename)]
  | Test ((_, _, test, e, None), _) -> [Def (Fresh "Test", None, of_test test k e)]
  | Test ((_, _, test, e, Some x), _) -> [Def (Normal x, None, of_test test k e)]
  | Let (_, [(_, Pvar Some name, _)]) when List.mem name remove_defs ->
     [Comment (sprintf "Definition of %s already included in the prelude" name)]
  | Let (_, bindings) ->
     let f : AST.binding -> _ = function
       | (_, Pvar None, exp) -> Def (Fresh "_", None, translate_exp k exp)
       | (_, Pvar Some name, exp) -> Def (Normal name, None, translate_exp k exp)
       | (_, Ptuple _, _) -> invalid_arg "toplevel let with tuple"
     in List.map f bindings
  | Rec (loc, bds, Some test) ->
     translate_instr k parse_file (Rec (loc, bds, None)) @
       translate_instr k parse_file (Test (test, Check))
  | Rec (_, bindings, None) ->
     let f : AST.binding -> _ = function
       | (_, Pvar (Some name), exp) -> (name, Fresh (name ^ "cons"), translate_exp k exp)
       | (_, Pvar None, _) -> invalid_arg "nameless let rec"
       | (_, Ptuple _, _) -> invalid_arg "tuple in let rec"
     in [Inductive (List.map f bindings)]
  | WithFrom (_, var, exp) -> [Withfrom (var, Fresh ("set_" ^ var), translate_exp k exp)]
  | UnShow    _ -> []
  | Show      _ -> []
  | ShowAs    _ -> []
  | Procedure _ -> []
  | InsMatch  _ -> invalid_arg "InsMatch"
  | Call      _ -> invalid_arg "Call"
  | Enum      _ -> invalid_arg "Enum"
  | Forall    _ -> invalid_arg "Forall"
  | Debug     _ -> invalid_arg "Debug"
  | Events    _ -> invalid_arg "Events"

let translate_instrs keepnotations parse instrs =
  List.concat (List.map (translate_instr keepnotations parse) instrs)

(** Transform a list of instructions with Fresh-marked names to
   instructions with normal string names *)

let resolve_fresh (l : name instr list) : string instr list =
  let open StringSet in
  let fv = function Normal x -> [x] | Fresh _ -> [] in
  let seen = ref (free_vars_of_instrs fv l) in
  let fresh x = 
    let x' = first (name_like x) (fun y -> not (mem y !seen)) in
    seen := add x' !seen;
    x'
  in
  let freshen = function Normal x -> x | Fresh x -> fresh x in
  let resolve : name instr -> string instr = function
    | Def (x, ty, e) -> Def (freshen x, ty, e)
    | Axiom (x, e) -> Axiom (freshen x, e)
    | Inductive defs ->
       Inductive (List.map (fun (x, n, e) -> (x, freshen n, e)) defs)
    | Withfrom (s, s', e) -> Withfrom (s, freshen s', e)
    | Comment s -> Comment s
  in
  List.map resolve l


(** Remove WithFrom -- needs to be done after resolve_fresh *)

let remove_withfrom (l : string instr list) : string instr list =
  let f : string instr -> string instr list = function
    | Withfrom (x, set, e) ->
       [Axiom (set, App_(Cst "sig", e));
        Def (x, None, App_(Cst "proj1_sig", Var_ set))]
    | i -> [i]
  in
  List.concat (List.map f l)


(** Shadowing *)

let resolve_shadowing defined (instrs : string instr list) : string instr list =
  let defined = ref defined in
  let visible = free_vars_of_instrs (fun x -> [x]) instrs in
  let renaming = ref StringMap.empty in
  let renamings = ref StringMap.empty in
  let ( += ) r (x, y) = r := StringMap.add x y !r in
  let new_name_for x =
    if StringSet.mem x !defined then
      let x' = fresh x (StringSet.union visible !defined) in
      renaming += (x, x');
      renamings += (x, x' :: StringMap.safe_find [] x !renamings);
      x'
    else
      x
  in
  let def x =
    let x' = new_name_for x in
    defined := StringSet.add x' !defined;
    x'
  in
  let sub e = subst_with_var !renaming e in
  let rename = function
    | Def (x, ty, e) -> let e = sub e in Def (def x, ty, e)
    | Axiom (x, e) -> let e = sub e in Axiom (def x, e)
    | Inductive defs ->
       defs
       |> List.map (fun (x, y, e) -> (def x, def y, e))
       |> List.map (fun (x, y, e) -> (x, y, sub e))
       |> fun d -> Inductive d
    | Withfrom (x, y, e) -> let e = sub e in Withfrom (def x, def y, e)
    | Comment s          -> Comment s
  in
  let instrs = List.map rename instrs in
  let com =
    !renamings
    |> StringMap.bindings
    |> List.map
         (fun (x, xs) ->
           sprintf
             "\n  %s -> %s"
             x (String.concat ", " (List.rev xs)))
    |> function
      | [] -> []
      | warnings ->
         [Comment ("Warning: the following renamings occurred:"
                   ^ String.concat "" warnings)]
  in
  instrs @ com


(** Removing try/with *)

let rec assert_notry =
  let f = assert_notry in
  function
  | Var_ x          -> Var_ x
  | Cst s           -> Cst s
  | App_(e1, e2)    -> App_(f e1, f e2)
  | Fun_(xs, e)     -> Fun_(xs, f e)
  | Let_(x, e1, e2) -> Let_(x, f e1, f e2)
  | Fix (x, xs, e)  -> Fix (x, xs, f e)
  | Tup es          -> Tup (List.map f es)
  | Op1 (o, e1)     -> Op1 (o, f e1)
  | Op2 (o, e1, e2) -> Op2 (o, f e1, f e2)
  | Try_ _          -> failwith "nested try .. with are ambiguous"
  | Annot (s, e)    -> Annot (s, f e)

let remove_trywith defined : string instr list -> string instr list =
  let open StringSet in
  let rec rmtry defined (e : exp) : exp =
    let f = rmtry defined in
    let fnewdef xs = rmtry (List.fold_right add xs defined) in
    match e with
    | Var_ x          -> Var_ x
    | Cst s           -> Cst s
    | App_(e1, e2)    -> App_(f e1, f e2)
    | Fun_(xs, e)     -> Fun_(xs, fnewdef xs e)
    | Let_(x, e1, e2) -> Let_(x, f e1, fnewdef [x] e2)
    | Fix (x, xs, e)  -> Fix (x, xs, fnewdef (x :: xs) e)
    | Tup es          -> Tup (List.map f es)
    | Op1 (o, e1)     -> Op1 (o, f e1)
    | Op2 (o, e1, e2) -> Op2 (o, f e1, f e2)
    | Try_ (e1, e2)    -> let s = pprint_exp e in
                         if subset (free_vars e1) defined
                         then Annot ("successful: "^ s, assert_notry e1)
                         else Annot ("failed: "^ s, f e2)
    | Annot (s, e)    -> Annot (s, f e)
  in
  (* TODO: replace with commandline-arguments and also the "uses" *)
  let defined = ref defined in
  let rmtry e = rmtry !defined e in
  let define x = defined := add x !defined in
  let def x = define x; x in
  List.map (function
      | Def (x, ty, e) -> let e = rmtry e in Def (def x, ty, e)
      | Axiom (x, e) -> let e = rmtry e in Axiom (def x, e)
      | Inductive defs ->
         List.iter (fun (x, y, _) -> define x; define y) defs;
         Inductive (List.map (fun (x, y, e) -> (x, y, rmtry e)) defs)
      | Withfrom (x, y, e)    -> let e = rmtry e in Withfrom (def x, def y, e)
      | Comment s -> Comment s)


(** Behaves as [f] but checks injectivity where it is called *)

let check_injectivity (print : 'a -> string) (f : string -> 'a) : string -> 'a =
  let open StringMap in
  let inv = ref empty in
  fun x ->
    let y = f x in
    begin match find y !inv with
    | exception Not_found -> inv := add y x !inv
    | x' when x = x' -> ()
    | x' ->
       failwith (sprintf "names %s and %s both mapped to %s" x' x (print y))
    end;
    y

(** Transforms chararacters '-' and '.' in identifiers and check that
   it introduces no conflict *)

let resolve_charset : string instr list -> string instr list =
  let fix_name = String.map (function '-' | '.' -> '_' | c -> c) in
  let fx = check_injectivity (fun s -> s) fix_name in
  let rec fe : exp -> exp = function
  | Var_ x          -> Var_ (fx x)
  | Cst s           -> Cst s
  | App_(e1, e2)    -> App_(fe e1, fe e2)
  | Fun_(xs, e)     -> Fun_(List.map fx xs, fe e)
  | Let_(x, e1, e2) -> Let_(fx x, fe e1, fe e2)
  | Fix (x, xs, e)  -> Fix (fx x, List.map fx xs, fe e)
  | Tup es          -> Tup (List.map fe es)
  | Op1 (o, e1)     -> Op1 (o, fe e1)
  | Op2 (o, e1, e2) -> Op2 (o, fe e1, fe e2)
  | Try_ (e1, e2)   -> Try_ (fe e1, fe e2)
  | Annot (s, e)    -> Annot (s, fe e)
  in
  List.map
    (function
     | Def (x, ty, e) -> Def (fx x, ty, fe e)
     | Axiom (x, e) -> Axiom (fx x, fe e)
     | Inductive l ->
        Inductive (List.map (fun (x, y, e) -> (fx x, fx y, fe e)) l)
     | Withfrom (x, y, e) -> Withfrom (fx x, fx y, fe e)
     | Comment s -> Comment s)


(** Get information on which names are defined, used before any
   definition, or tried (and not used) before any definition *)

type naming = {
    defines : StringSet.t;
    uses : StringSet.t;
    tries : StringSet.t;
  }

let naming_information (instructions : string instr list) : naming =
  let open StringSet in
  let defined, used, tried = ref empty, ref empty, ref empty in
  let (+) = union in
  let (-) = diff in
  let (+=) r x = r := !r + x in
  let use e =
    used += (used_vars e - !defined);
    tried += (tried_vars e - !defined);
  in
  let def x = defined += singleton x in
  begin List.iter
    (function
     | Def (x, _, e) -> use e; def x
     | Axiom (x, e) -> use e; def x
     | Withfrom (x, y, e) -> use e; def x; def y
     | Comment _ -> ()
     | Inductive l ->
        List.iter (fun (x, y, _) -> def x; def y) l;
        List.iter (fun (_, _, e) -> use e) l)
    instructions
  end;
  { defines = !defined;
    uses    = !used;
    tries   = !tried }


(** From cat-like instructions to coq-like instructions *)

let transform_instrs (l : name instr list) : string instr list =
  let open StringSet in
  let l = resolve_fresh l in
  let l = remove_withfrom l in
  let l = special_cases l in
  
  let { uses; tries; _ } = naming_information l in
  
  (* Warning about names being tried but not defined *)
  let ambiguous = elements (diff tries uses) in
  let warning =
    ambiguous
    |> String.concat ", "
    |> sprintf "Warning: ambiguous set of variables {%s} only used \
                inside try/with, before any definition, will be \
                considered a priori not defined"
  in
  (* if ambiguous <> [] then fprintf stderr "%s\n%!" warning; *)
  let l = if ambiguous = [] then l else Comment warning :: l in

  (* Warning about names being used but not in the prelude nor in on-demand *)
  let prelude = of_list in_prelude in
  let ondemand = of_list (List.map fst on_demand) in
  let notfound = elements (diff uses (union prelude ondemand)) in
  let warning =
    notfound
    |> String.concat ", "
    |> sprintf "set of variables {%s} used but not defined in the \
                prelude nor is providable on demand"
  in
  if notfound <> [] then failwith warning;
  (* if notfound <> [] then fprintf stderr "%s\n%!" warning; *)
  let l = if notfound = [] then l else Comment warning :: l in
  
  (* Handling on-demand definitions/axioms *)
  let prelude = of_list in_prelude in
  let ondemand = elements (inter (diff uses prelude) ondemand) in
  let warning =
    ondemand
    |> String.concat ", "
    |> sprintf "Warning: set of variables {%s} used but not defined \
                in the prelude, but will be be provided on demand"
  in
  (* if ondemand <> [] then fprintf stderr "%s\n%!" warning; *)
  let l = if ondemand = [] then l else Comment warning :: l in
  let provide x = Axiom (x, Cst (List.assoc x on_demand)) in
  let ondemand_definitions = List.map provide ondemand in
  
  let defined_before = union uses (union prelude (of_list ondemand))  in
  l
  |> resolve_shadowing defined_before
  |> remove_trywith defined_before
  |> (@) ondemand_definitions
  |> resolve_charset


let read_file filename : string list = 
  let lines = ref [] in
  let chan = open_in filename in
  try
    while true do
      lines := input_line chan :: !lines
    done; assert false
  with End_of_file ->
    close_in chan;
    List.rev !lines

let pprint_coq_model
      (keepnotations : bool)
      (prelude : string list)
      (parse_file : string -> AST.t)
      (model : AST.t) : string =
  let parse fname = let (_, _, i) = parse_file fname in i in
  let (_, name, instrs) = model in
  
  (* We automatically include stdlib.cat *)
  let instrs = AST.Include (TxtLoc.none, "stdlib.cat") :: instrs in

  (* Line-by-line translation of cat commands *)
  let instrs = translate_instrs keepnotations parse instrs in
  
  (* More global transformations *)
  let instrs = transform_instrs instrs in
  
  let comment s = pprint_instr (Comment s) in
  
  [
    comment (sprintf "Translation of model %s" name);
    comment "Import of prelude";
    List.map ((^) "  ") prelude;
    comment "End of prelude";
    if keepnotations then ["Open Scope cat_scope."] else [];
    List.concat (List.map (pprint_instr) instrs);
    comment (sprintf "End of translation of model %s" name)
  ]
  |> List.concat |> String.concat "\n"


(** Read commandline options *)

let args, debug, notations, output_file, includes, usage, convertfilename =
  let includes = ref [] in
  let debug = ref false in
  let notations = ref true in
  let output_file = ref "-" in
  let args = ref [] in
  let convertfilename = ref false in
  let get_cmd_arg s = args := s :: !args in
  let prog =
    if Array.length Sys.argv > 0 then
      Filename.basename Sys.argv.(0)
    else "cat2coq7"
  in
  let usage = sprintf "Usage: %s [options]* <file.cat>" prog in
  let options = [
      ("-I",
       Arg.String (fun s -> includes := !includes @ [s]),
       "<dir> add <dir> to search path");
      ("-debug",
       Arg.Unit (fun () -> debug := true),
       "debug messages, e.g. for parsing");
      ("-nonotations",
       Arg.Unit (fun () -> notations := false),
       "do not keep notations, uses regular identifiers instead") ;
      ("-convertfilename",
       Arg.Unit (fun () -> convertfilename := true),
       "do not read any file, simply convert the filename to a coq-compatible filename (-, ., mapped to _)") ;
      ("-o", Arg.String
               (function
                | "-" -> output_file := "-"
                | _ -> failwith "not implemented"), (* TODO *)
       "<filename> generated file name, - for stdtout, default stdout") ;
    ] in
  Arg.parse options get_cmd_arg usage;
  (!args, !debug, !notations, !output_file, !includes, usage, !convertfilename)

let libfind =
  let module ML =
    MyLib.Make
      (struct
        let includes = includes
        let env = Some "HERDLIB"
        let libdir = Filename.concat Version.libdir "herd"
        let debug = debug
      end) in ML.find

module Parser =
  ParseModel.Make
    (struct
      let debug = false
      let libfind = libfind
    end)

let handle_filename fname =
  let fix_name = String.map (function '-' | '.' | '+' -> '_' | c -> c) in
  if convertfilename then
    if Filename.check_suffix fname ".cat" then
      printf "%s\n" (fix_name (Filename.chop_suffix fname ".cat") ^ ".v")
    else
      (eprintf "not a .cat file name, unsure what to convert\n"; exit 1)
  else
    let prelude = read_file (libfind "prelude_cat2coq.v") in
    printf "%s\n"
      (pprint_coq_model
         notations
         prelude
         Parser.parse
         (Parser.parse fname))

let () =
  try
    match args with
    | [] -> printf "%s\n" usage
    | [fname] -> handle_filename fname
    | _ -> eprintf "error: only one .cat file is supported at the moment"; exit 1
  with
  | Misc.Fatal s | Failure s ->
     eprintf "Error: %s\n" s;
     exit 1
