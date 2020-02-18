open Printf

(** Functions on lists *)

let rec filter_map (f : 'a -> 'b option) : 'a list -> 'b list =
  function
  | [] -> []
  | a :: l ->
     match f a with
     | None -> filter_map f l
     | Some b -> b :: filter_map f l

let rec fold_right1 (f : 'a -> 'a -> 'a) : 'a list -> 'a =
  function
  | [] -> invalid_arg "fold_right1"
  | [x] -> x
  | x :: xs -> f x (fold_right1 f xs)

let extract_from_list (f : 'a -> 'b option) : 'a list -> ('a list * 'b list) =
  let rec extr al bl = function
    | [] -> (List.rev al, List.rev bl)
    | a :: l ->
       match f a with
       | None -> extr (a :: al) bl l
       | Some b -> extr al (b :: bl) l
  in extr [] []

let split_on_char sep s =
  let open String in
  let r = ref [] in
  let j = ref (length s) in
  for i = length s - 1 downto 0 do
    if unsafe_get s i = sep then begin
      r := sub s (i + 1) (!j - i - 1) :: !r;
      j := i
    end
  done;
  sub s 0 !j :: !r

let assoc_inv : 'b -> ('a * 'b) list -> 'a =
  fun b l -> List.assoc b (List.map (fun (a, b) -> (b, a)) l)

(** Coq-encodable expressions + try/with *)

type notation = Non | Cat | Kat (* | Atbr *)
let notation_names = [("none", Non); ("cat", Cat); ("kat", Kat)(* ; ("atbr", Atbr) *)]

let pprint_op1 : AST.op1 -> string -> string =
  let open AST in
  function
  | Inv -> sprintf "%s^-1"
  | Comp -> sprintf "~%s"
  | ToId -> sprintf "[%s]"
  | Plus -> sprintf "%s^+"
  | Star -> sprintf "%s^*"
  | Opt -> sprintf "%s?"

type op2 = Union | Seq | Inter | Sub | Cartes | Cast | And | Arr

let pprint_op2 = function
  | Union -> "∪"
  | Seq -> ";;"
  | Inter -> "∩"
  | Sub -> "\\"
  | Cartes -> "*"
  | Cast -> ":"
  | And -> "/\\"
  | Arr -> "->"

type exp =
  | Var of string
  | Cst of string (* non-substitutable variable *)
  | App of exp * exp
  | Fun of string list * exp
  | Let of string * exp * exp
  | Fix of string * string list * exp
  | Tup of exp list
  | Op1 of AST.op1 * exp
  | Op2 of op2 * exp * exp
  | Try of exp * exp
  | Annot of string * exp

let rec free_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = free_vars in
  function
  | Var x -> singleton x
  | Cst x -> singleton x
  | App (e1, e2) -> f e1 + f e2
  | Fun (xs, e) -> List.fold_right remove xs (f e)
  | Let (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try (e1, e2) -> f e1 + f e2
  | Annot (_, e) -> f e


(** Variables appearing in [try _] *)

let rec tried_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = tried_vars in
  function
  | Var _ -> empty
  | Cst _ -> empty
  | App (e1, e2) -> f e1 + f e2
  | Fun (xs, e) -> List.fold_right remove xs (f e)
  | Let (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try (e1, e2) -> free_vars e1 + f e2
  | Annot (_, e) -> f e


(** Free variables not counting the ones in [try _] *)

let rec used_vars : exp -> StringSet.t =
  let open StringSet in
  let ( + ) = union in
  let f = used_vars in
  function
  | Var x -> singleton x
  | Cst _ -> empty
  | App (e1, e2) -> f e1 + f e2
  | Fun (xs, e) -> List.fold_right remove xs (f e)
  | Let (x, e1, e2) -> f e1 + remove x (f e2)
  | Fix (x, xs, e) -> f (Fun (x :: xs, e))
  | Tup es -> unions (List.map f es)
  | Op1 (_, e1) -> f e1
  | Op2 (_, e1, e2) -> f e1 + f e2
  | Try (_, e2) -> f e2
  | Annot (_, e) -> f e


(** [fresh x vars] returns a name like [x] not belonging to [vars] *)

let name_like (x : string) : int -> string = function
  | 0 -> x
  | n -> x ^ "_" ^ string_of_int (n - 1)

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
      let body' = subst (StringMap.singleton x (Var x')) body in
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
  | Var x           -> StringMap.safe_find (Var x) x sub
  | Cst s           -> Cst s
  | App (e1, e2)    -> App (subst sub e1, subst sub e2)
  | Fun (xs, e)     -> let (xs, e, sub) = abs' xs e sub in
                       Fun(xs, subst sub e)
  | Let (x, e1, e2) -> let e1 = subst sub e1 in (* x not binding in e1 *)
                       let (x, e2, sub) = abs x e2 sub in
                       Let (x, e1, subst sub e2)
  | Fix (x, xs, e)  -> let (xxs, e, sub) = abs' (x :: xs) e sub in
                       Fix (List.hd xxs, List.tl xxs, subst sub e)
  | Tup es          -> Tup (List.map (subst sub) es)
  | Op1 (o, e1)     -> Op1 (o, subst sub e1)
  | Op2 (o, e1, e2) -> Op2 (o, subst sub e1, subst sub e2)
  | Try (e1, e2)    -> Try (subst sub e1, subst sub e2)
  | Annot (s, e)    -> Annot (s, subst sub e)

let subst_with_var (sub : string StringMap.t) : exp -> exp =
  subst (StringMap.map (fun x -> Var x) sub)


(** Pretty-printing, with aggressive currying *)

let level_op2 = function
  | Union -> 70
  | Seq -> 55
  | Inter -> 51
  | Sub -> 45
  | Cartes -> 40
  | Cast -> 2
  | And -> 80
  | Arr -> 99

let right_associative = function
  | Union | Seq | Inter | And | Arr -> true
  | Sub | Cartes | Cast -> false

let rec cascade_op (o : op2) : exp -> exp list =
  function
  | Op2 (o', e1, e2) when o = o' -> e1 :: cascade_op o e2
  | e -> [e]

let rec pprint_exp verbosity e =
  let p = pprint_exp verbosity in
  let ppar e = match e with
    | Var x | Cst x -> x
    | Op1 (AST.ToId, _) -> p e
    | _ -> "(" ^ p e ^ ")"
  in
  let open String in
  match e with
  | Var x -> x
  | Cst s -> s
  | App (App (e1, e2), e3) -> ppar e1 ^ " " ^ ppar e2 ^ " " ^ ppar e3
  | App (e1, Tup es) -> ppar e1 ^ " " ^ concat " " (List.map ppar es)
  | App (e1, e2) -> ppar e1 ^ " " ^ ppar e2
  | Op1 (o, e1) -> pprint_op1 o (ppar e1)
  | Op2 (o, e1, e2) ->
     if right_associative o then
       concat (" " ^ pprint_op2 o ^ " ") (List.map ppar (e1 :: cascade_op o e2))
     else
       sprintf "%s %s %s" (ppar e1) (pprint_op2 o) (ppar e2)
  | Tup l -> "(" ^ (concat ", " (List.map p l)) ^ ")"
  | Fun (xs, e) -> sprintf "fun %s => %s" (concat " " xs) (p e)
  | Fix (f, xs, body) -> sprintf "fix %s %s := %s" f (concat " " xs) (p body)
  | Let (x, e1, e2) -> sprintf "let %s := %s in %s" x (p e1) (p e2)
  | Annot (_, e) when verbosity <= 0 -> p e
  | Annot (comment, e) -> sprintf "(*%s*) %s" comment (p e)
  | Try (e1, e2) -> sprintf "try %s with %s" (p e1) (p e2)

let rec has_notations e : bool =
  let f = has_notations in
  match e with
  | Var _ | Cst _ -> false
  | Op1 (_, _) | Op2 (_, _, _) -> true
  | Fun(_, e) | Fix (_, _, e) | Annot (_, e) -> f e
  | App (e1, e2) | Let (_, e1, e2) | Try (e1, e2) -> f e1 || f e2
  | Tup es -> List.exists f es

let pprint_exp_scope verbosity e =
  if has_notations e
  then "(" ^ pprint_exp verbosity e ^ ")%cat"
  else pprint_exp verbosity e

let print_exp = pprint_exp_scope


(** Instructions, parameterized by a type for possibly-generated names *)

type definition_kind = Normal_definition | Test_definition | Condition

type 'name instr =
  | Def of 'name * string option (* possible type annotation*) * exp * definition_kind
  | Variable of 'name * exp (* section variable *)
  | Inductive of (string * 'name * exp) list
  | Withfrom of string * 'name * exp
  | Comment of string
  | Command of string

type name = Fresh of string | Normal of string


(** Free and defined variables mentioned in an instruction *)

let free_vars_of_instr (fv: 'a -> string list) : 'a instr -> StringSet.t =
  let open StringSet in
  let (+) xs set = List.fold_right add xs set in
  (* let (+) s = function Normal x -> add x s | Fresh _ -> s in *)
  function
  | Def (x, _, e, _) -> fv x + free_vars e
  | Variable (x, e) -> fv x + free_vars e
  | Inductive defs ->
     unions (List.map (fun (x, y, e) -> [x] + (fv y + free_vars e)) defs)
  | Withfrom (x, y, e) -> [x] + (fv y + free_vars e)
  | Comment _ -> empty
  | Command _ -> empty

let free_vars_of_instrs (fv: 'a -> string list) (l : 'a instr list) =
  StringSet.unions (List.map (free_vars_of_instr fv) l)


(** Given as aguments to the model *)

let candidate_fields =
  ["R"; "W"; "IW"; "FW"; "B"; "RMW"; "F";
   "rf"; "po"; "int"; "ext"; "loc"; "addr"; "data"; "ctrl"; "amo"]

let imports_candidate_fields : string instr list =
  List.map
    (fun x -> Def (x, None, App (Cst x, Cst "c"), Normal_definition))
    (candidate_fields @ ["unknown_set"; "unknown_relation"])

let rel_or_set s =
  if String.length s > 0 && 'a' <= s.[0] && s.[0] <= 'z'
  then "relation"
  else "set"

let axioms =
  List.map
    (fun x -> Variable (x, App (Cst (rel_or_set x), Cst "events")))
    candidate_fields


(** Before generated code *)

let name_of_candidate = "c"

let start_definitions =
  [
    Variable (name_of_candidate, Cst "candidate");
    Def ("events", None, App (Cst "events", Cst "c"), Normal_definition);
    Command "Instance SetLike_set_events : SetLike (set events) := SetLike_set events.";
    Command "Instance SetLike_relation_events : SetLike (relation events) := SetLike_relation events."
  ]


(** After generated imports from candidate *)

let middle_definitions =
  [
    Def ("M", None, Op2 (Union, Var "R", Var "W"), Normal_definition);
    Def ("emptyset", Some "set events", Cst "empty", Normal_definition);
    Def ("classes_loc", Some "set events -> set (set events)",
         Cst "fun S Si => forall x y, Si x -> Si y -> loc x y",
         Normal_definition)
        (* TODO FIX classes_loc which is obv. wrong *)
  ]


(** After generated code *)

let end_text instrs =
  let all_axiom_relations =
    filter_map (function Variable (x, _) -> Some x | _ -> None) instrs
    |> List.filter ((<>) name_of_candidate)
  in
  let empty_witness_cond =
    List.mem
      (Def ("witness_conditions", None, Cst "True", Normal_definition))
      instrs
  in
  let empty_model_cond =
    List.mem
      (Def ("model_conditions", None, Cst "True", Normal_definition))
      instrs
  in

  let relations = String.concat " " all_axiom_relations in
  sprintf
"
Definition valid (c : candidate) := %s%s.
"
  (if empty_witness_cond then "" else sprintf "
  exists %s : relation (events c),
    witness_conditions c %s /\\
    " relations relations)
  (if empty_model_cond then "True" else sprintf "model_conditions c %s" relations)



(** Definitions that are too complex to translate, so we remove them
   and define them in the prelude *)

let definitions_to_remove =
  ["co_locs"; "cross"; "map"]


(** Definitions that are in the prelude but can be shadowed *)

let defined_in_prelude =
  definitions_to_remove @
    [ "universal"; "complement"; "union"; "intersection";
      "diff"; "rel_seq"; "rel_inv"; "cartesian"; "incl"; "id";
      "domain"; "range"; "diagonal"; "acyclic"; "is_empty";
      "irreflexive"; "clos_trans"; "clos_refl_trans"; "clos_refl";
      "set"; "relation"; "not"; "StrictTotalOrder"; "linearisations";
      "set_flatten"; "classes-loc"; "_";  "emptyset";
      "empty"; "sig"; "M" ]

let unknown_def x =
  Def (x, None,
       App (Cst ("unknown_" ^ rel_or_set x),
             Cst (sprintf "\"%s\"" x)),
       Normal_definition)

let unknown_axiom x =
  Variable (x, App (Cst (rel_or_set x), Cst "events"))


(** Type annotations for cases for which Cst fails at inference. This
   is less useful since currying has become the norm *)

let force_type : string -> string option =
  function
  | "toid" -> Some "relation events"
  | _ -> None

let special_cases =
  List.map @@
    function
    | Def (x, _, e, t) -> Def (x, force_type x, e, t)
    | instr -> instr


(** Printing instructions *)

let t = ref 0

let pprint_instr verbosity (i : string instr) : string list =
  let opt = function None -> "" | Some s -> ": " ^ s ^ " " in
  let indent = String.make !t ' ' in
  let pprint_exp = pprint_exp verbosity in
  match i with
  | Comment "INDENT" -> if verbosity >= 1 then t := !t + 2; []
  | Comment "DEDENT" -> if verbosity >= 1 then t := !t - 2; []
  | Comment _ when verbosity <= 0 -> []
  | _ ->
     [indent ^
       match i with
       | Comment s -> sprintf "(* %s *)" s
       | Command s -> s
       | Def (x, ty, Fun (xs, e), _) ->
          sprintf "Definition %s %s %s:= %s."
            x (String.concat " " xs) (opt ty) (pprint_exp e)
       | Def (x, ty, e, _) -> sprintf "Definition %s %s:= %s." x (opt ty) (pprint_exp e)
       | Variable (x, e) -> sprintf "Variable %s : %s." x (pprint_exp e)
       | Inductive defs ->
          let f (x, cx, e) =
            sprintf "%s : relation _ := %s : incl (%s) %s" x cx (pprint_exp e) x
          in sprintf "Inductive %s."
               (String.concat ("\n" ^ indent ^ "  with ")
                  (List.map f defs))
       | Withfrom _ ->
          invalid_arg "withfroms should have been eliminated before"
     ]


(** Eliminating base operators *)

let exp_of_op1 : AST.op1 -> exp =
  let app (x, y) = App (x, y) in
  let open AST in
  function
  | Plus -> app (Cst "clos_trans", Cst "_")
  | Star -> app (Cst "clos_refl_trans", Cst "_")
  | Opt -> app (Cst "clos_refl", Cst "_")
  | Comp -> Cst "complement"
  | Inv -> Cst "rel_inv"
  | ToId -> Cst "diagonal"

let translate_op1 (o : AST.op1) e = App (exp_of_op1 o, e)

let translate_op1_keep (o : AST.op1) e =
  Op1 (o, e)

let rec translate_op2 (o : AST.op2) (es : exp list) : exp =
  let app2 x e1 e2 = App (App (Cst x, e1), e2) in
  match o, es with
  | AST.Union, [] -> Cst "empty"
  | AST.Union, [e] -> e
  | AST.Union, (e :: l) -> app2 "union" e (translate_op2 AST.Union l)
  | AST.Inter, [e1; e2] -> app2 "intersection" e1 e2
  | AST.Diff, [e1; e2] -> app2 "diff" e1 e2
  | AST.Cartesian, [e1; e2] -> app2 "cartesian" e1 e2
  | AST.Add, [e1; e2] -> app2 "add_element" e1 e2
  | AST.Seq, [e] -> e
  | AST.Seq, (e :: l) -> app2 "rel_seq" e (translate_op2 AST.Seq l)
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
  | AST.Add, [_; _] -> failwith "adding elements to lists not in the supported subset of cat"
  | AST.Seq, [e] -> e
  | AST.Seq, (e :: l) -> Op2 (Seq, e, translate_op2_keep AST.Seq l)
  | _ -> translate_op2 o es


(** Translating expressions *)

let vars_of_pat : AST.pat -> string list =
  let f = function None -> "_" | Some x -> x in
  function AST.Pvar p -> [f p] | AST.Ptuple ps -> List.map f ps

let rec translate_exp (notation : notation) (e : AST.exp) : exp =
  let f e = translate_exp notation e in
  let invalid_arg s = invalid_arg ("translate_exp: " ^ s) in
  let rec lets e2 = function
    | [] -> e2
    | (x, e1) :: l -> Let (x, e1, lets e2 l)
  in
  let nicer_binding = function
    | (_, AST.Pvar None, e1) -> ("_", e1)
    | (_, AST.Pvar (Some x), e1) -> (x, e1)
    | (_, AST.Ptuple _, _) -> invalid_arg "destructuring binding"
  in
  let (op1, op2) =
    match notation with
    | Cat -> (translate_op1_keep, translate_op2_keep)
    | Kat -> failwith "kat unsupported"
    | Non -> (translate_op1, translate_op2)
  in
  let var x = Var x in
  match e with
  | AST.Konst (_, AST.Empty _) -> Cst "empty"
  | AST.Konst (_, AST.Universe _) -> Cst "universal"
  | AST.Tag (_, tag) -> Cst (sprintf "Tag \"%s\"" tag)
  | AST.Var (_, x) -> var x
  | AST.Op1 (_, o, exp) -> op1 o (f exp)
  | AST.Op (_, o, args) -> op2 o (List.map f args)
  | AST.App (_, e1, e2) -> App (f e1, f e2)
  | AST.Try (_, e1, e2) -> Try (f e1, f e2)
  | AST.Bind (_, bindings, e2) ->
     bindings
     |> List.map nicer_binding
     |> List.map (fun (x, e1) -> (x, f e1))
     |> lets (f e2)
  | AST.BindRec (_, bindings, e2) ->
     (* Has never been tested! *)
     begin match bindings with
     | [] -> invalid_arg "empty let rec in"
     | _ :: _ :: _ -> invalid_arg "mutual let rec in"
     | [(_, AST.Ptuple _, _)] -> invalid_arg "destructuring in let rec"
     | [(_, AST.Pvar None, _)] -> invalid_arg "nameless let rec"
     | [(_, AST.Pvar (Some name), (AST.Fun (_, pat, body, _, _)))] ->
        Let (name, Fix (name, vars_of_pat pat, f body), f e2)
     | [(_, AST.Pvar _, _)] -> invalid_arg "let rec in with no argument"
     end
  | AST.Fun (_, pat, exp, _name, _freevars) ->
     Fun (vars_of_pat pat, f exp)
  | AST.ExplicitSet (_, []) -> Op2 (Cast, Cst "empty", App (Cst "set", Cst "_"))
  | AST.ExplicitSet (_, [e]) -> App (Cst "singleton", f e)
  | AST.ExplicitSet (_, (_ :: _)) -> failwith "adding elements to lists not in the supported subset of cat"
  | AST.Match _ -> invalid_arg "match not implemented"
  | AST.MatchSet _ -> invalid_arg "matchset not implemented"
  | AST.If _ -> invalid_arg "if"


(** Translate a kind of test into an expression *)
let of_test (t : AST.test) k (e : AST.exp) : exp =
  let e = translate_exp k e in
  let f (t : AST.do_test) = Cst (match t with
    | AST.Acyclic -> "acyclic"
    | AST.Irreflexive -> "irreflexive"
    | AST.TestEmpty -> "is_empty")
  in
  match t with
  | AST.Yes t -> App (f t, e)
  | AST.No t -> App (Cst "not", (App (f t, e)))


(** Expand includes *)

let rec expand_include parse_file is =
  let expand_one = function
    | AST.Include (_, filename) -> expand_include parse_file (parse_file filename)
    | x -> [x]
  in
  List.(concat @@ map expand_one is)


(** Remove unused definitions (lib/AST's syntax)*)

let filter_unused_defs instrs =
  let test_exps = filter_map
                (function AST.Test ((_, _, _, e, _), _) -> Some e | _ -> None)
                instrs
  in
  let concat = List.fold_left StringSet.union StringSet.empty in
  let vars_of_exps list = concat @@ List.map (ASTUtils.free_body []) list in
  let needed = ref (vars_of_exps test_exps) in
  let filter = function
    | AST.Let (_, list)
    | AST.Rec (_, list, _) ->
      let pats = List.concat @@ List.map (fun (_, x, _) -> vars_of_pat x) list in
       if List.exists (fun s -> StringSet.mem s !needed) pats then begin
          let exps = List.map (fun (_, _, e) -> e) list in
          needed := StringSet.union !needed (vars_of_exps exps);
          true
         end
       else false
    | AST.WithFrom (_, _, exp) ->
       needed := StringSet.union !needed (vars_of_exps [exp]);
       true
    | _ -> true
  in List.rev @@ List.filter filter (List.rev instrs)


(** Remove unused definitions (this file's syntax)*)

let remove_unused ~(keepalive : string list) (is : string instr list) : string instr list =
  let open StringSet in
  let ( + ) = union in
  let rec clean keep = function
    | [] -> []
    (* Remove commands defining x when we do not need to keep x *)
    | ( Withfrom (x, _, _) | Variable (x, _) | Def (x, _, _, _)) :: is
         when not (mem x keep)
      -> clean keep is
    | Inductive defs :: is
         when List.for_all (function (x, _, _) -> not (mem x keep)) defs
      -> clean keep is
    (* Otherwise, we keep and add free variables to the set [keep] *)
    | (Withfrom (_, _, e) | Variable (_, e) as i) :: is -> i :: clean (free_vars e + keep) is
    | (Def (_, _, e, _) as i) :: is -> i :: clean (free_vars e + keep) is
    | (Inductive defs as i) :: is ->
       i :: clean (List.fold_left (+) keep (List.map (function (_, _, e) -> free_vars e) defs)) is
    | (Comment _ | Command _) as i :: is -> i :: clean keep is
  in
  List.rev (clean (of_list keepalive) (List.rev is))


(** Simple translation: cat instruction -> ~coq instruction *)

let rec translate_instr notation (i : AST.ins)
  : name instr list =
  let invalid_arg s = invalid_arg ("of_instr: " ^ s) in
  let open AST in
  match i with
  | Include (_, _) -> failwith "Include should have been expanded already"
  | Test ((_, _, test, e, None), _) ->
     [Def (Fresh "test", None, of_test test notation e, Test_definition)]
  | Test ((_, _, test, e, Some x), _) ->
     [Def (Normal x, None, of_test test notation e, Test_definition)]
  | Let (_, [(_, Pvar Some name, _)]) when List.mem name definitions_to_remove ->
     [Comment (sprintf "Definition of %s already included in the prelude" name)]
  | Let (_, bindings) ->
     let f : AST.binding -> _ = function
       | (_, Pvar None, exp) -> Def (Fresh "_", None, translate_exp notation exp, Normal_definition)
       | (_, Pvar Some name, exp) -> Def (Normal name, None, translate_exp notation exp, Normal_definition)
       | (_, Ptuple _, _) -> invalid_arg "toplevel let with tuple"
     in List.map f bindings
  | Rec (loc, bds, Some test) ->
     translate_instr notation (Rec (loc, bds, None)) @
       translate_instr notation (Test (test, Check))
  | Rec (_, bindings, None) ->
     let f : AST.binding -> _ = function
       | (_, Pvar (Some name), exp) -> (name, Fresh (name ^ "_c"), translate_exp notation exp)
       | (_, Pvar None, _) -> invalid_arg "nameless let rec"
       | (_, Ptuple _, _) -> invalid_arg "tuple in let rec"
     in [Inductive (List.map f bindings)]
  | WithFrom (_, var, exp) -> [Withfrom (var, Fresh ("set_" ^ var), translate_exp notation exp)]
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
    | Def (x, ty, e, t) -> Def (freshen x, ty, e, t)
    | Variable (x, e) -> Variable (freshen x, e)
    | Inductive defs ->
       Inductive (List.map (fun (x, n, e) -> (x, freshen n, e)) defs)
    | Withfrom (s, s', e) -> Withfrom (s, freshen s', e)
    | Comment s -> Comment s
    | Command s -> Command s
  in
  List.map resolve l


(** Remove WithFrom -- needs to be done after resolve_fresh *)

let remove_withfrom_axiom_set (l : string instr list) : string instr list =
  let add_arg e1 e2 =
    match e1 with
    | App (e1, Tup e2s) -> App (e1, Tup (e2s @ [e2]))
    | e1 -> App (e1, e2)
  in
  let eta_expanse x e = Fun ([x], add_arg e (Var x)) in
  let f : string instr -> string instr list = function
    | Withfrom (x, set, e) ->
       [Variable (set, App (Cst "sig", eta_expanse x e));
        Def (x, None, App (Cst "proj1_sig", Var set), Normal_definition)]
    | i -> [i]
  in
  List.concat (List.map f l)


let remove_withfrom (l : string instr list) : string instr list =
  let add_arg e1 e2 =
    match e1 with
    | App (e1, Tup e2s) -> App (e1, Tup (e2s @ [e2]))
    | e1 -> App (e1, e2)
  in
  let collect : string instr -> string instr list = function
    | Withfrom (x, set, e) ->
       [Variable (x, App (Cst "relation", Cst "events"));
        Def (set, None, add_arg e (Var x), Condition)]
    | i -> [i]
  in
  List.concat (List.map collect l)


(** Shadowing *)

let resolve_shadowing add_info defined (instrs : string instr list) : string instr list =
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
    | Def (x, ty, e, t) -> let e = sub e in Def (def x, ty, e, t)
    | Variable (x, e) -> let e = sub e in Variable (def x, e)
    | Inductive defs ->
       defs
       |> List.map (fun (x, y, e) -> (def x, def y, e))
       |> List.map (fun (x, y, e) -> (x, y, sub e))
       |> fun d -> Inductive d
    | Withfrom (x, y, e) -> let e = sub e in Withfrom (def x, def y, e)
    | Comment s          -> Comment s
    | Command s          -> Command s
  in
  let instrs = List.map rename instrs in
  let () =
    !renamings
    |> StringMap.bindings
    |> List.map
         (fun (x, xs) ->
           sprintf
             "\n  %s -> %s"
             x (String.concat ", " (List.rev xs)))
    |> function
      | [] -> ()
      | warnings ->
         add_info ("The following renamings occurred:" ^ String.concat "" warnings)
  in
  instrs


(** Removing try/with *)

let rec assert_notry =
  let f = assert_notry in
  function
  | Var x           -> Var x
  | Cst s           -> Cst s
  | App (e1, e2)    -> App (f e1, f e2)
  | Fun (xs, e)     -> Fun (xs, f e)
  | Let (x, e1, e2) -> Let (x, f e1, f e2)
  | Fix (x, xs, e)  -> Fix (x, xs, f e)
  | Tup es          -> Tup (List.map f es)
  | Op1 (o, e1)     -> Op1 (o, f e1)
  | Op2 (o, e1, e2) -> Op2 (o, f e1, f e2)
  | Try _           -> failwith "nested try .. with are ambiguous"
  | Annot (s, e)    -> Annot (s, f e)

let remove_trywith defined : string instr list -> string instr list =
  let open StringSet in
  let rec rmtry defined (e : exp) : exp =
    let f = rmtry defined in
    let fnewdef xs = rmtry (List.fold_right add xs defined) in
    match e with
    | Var x           -> Var x
    | Cst s           -> Cst s
    | App (e1, e2)    -> App (f e1, f e2)
    | Fun (xs, e)     -> Fun (xs, fnewdef xs e)
    | Let (x, e1, e2) -> Let (x, f e1, fnewdef [x] e2)
    | Fix (x, xs, e)  -> Fix (x, xs, fnewdef (x :: xs) e)
    | Tup es          -> Tup (List.map f es)
    | Op1 (o, e1)     -> Op1 (o, f e1)
    | Op2 (o, e1, e2) -> Op2 (o, f e1, f e2)
    | Try (e1, e2)    -> let s = pprint_exp 1 e in
                         if subset (free_vars e1) defined
                         then Annot ("successful: "^ s, assert_notry e1)
                         else Annot ("failed: "^ s, f e2)
    | Annot (s, e)    -> Annot (s, f e)
  in
  let defined = ref defined in
  let rmtry e = rmtry !defined e in
  let define x = defined := add x !defined in
  let def x = define x; x in
  List.map (function
      | Def (x, ty, e, t) -> let e = rmtry e in Def (def x, ty, e, t)
      | Variable (x, e) -> let e = rmtry e in Variable (def x, e)
      | Inductive defs ->
         List.iter (fun (x, y, _) -> define x; define y) defs;
         Inductive (List.map (fun (x, y, e) -> (x, y, rmtry e)) defs)
      | Withfrom (x, y, e)    -> let e = rmtry e in Withfrom (def x, def y, e)
      | Comment s -> Comment s
      | Command s -> Command s)


(** Collects conditions and gather them at the end *)

let conjunction_of_exps (l : exp list) : exp =
  if l = [] then
    Cst "True"
  else
    fold_right1 (fun x y -> Op2 (And, x, y)) l

let conjunction_of_vars (vars : string list) : exp =
  conjunction_of_exps (List.map (fun x -> Var x) vars)

let collect_conditions instrs : string instr list =
  (* Get the name of all the test declared *)
  let tests =
    filter_map
      (function Def (x, _, _, Test_definition) -> Some x | _ -> None)
      instrs
  in
  (* Extract the conditions on withfroms *)
  let (instrs, conditions) =
    extract_from_list
      (function Def (_, _, e, Condition) -> Some e | _ -> None)
      instrs
  in
  instrs @
    [Def ("witness_conditions", None, conjunction_of_exps conditions, Normal_definition);
     Def ("model_conditions", None, conjunction_of_vars tests, Normal_definition) ]


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
  | Var x           -> Var (fx x)
  | Cst s           -> Cst s
  | App (e1, e2)    -> App (fe e1, fe e2)
  | Fun (xs, e)     -> Fun (List.map fx xs, fe e)
  | Let (x, e1, e2) -> Let (fx x, fe e1, fe e2)
  | Fix (x, xs, e)  -> Fix (fx x, List.map fx xs, fe e)
  | Tup es          -> Tup (List.map fe es)
  | Op1 (o, e1)     -> Op1 (o, fe e1)
  | Op2 (o, e1, e2) -> Op2 (o, fe e1, fe e2)
  | Try (e1, e2)    -> Try (fe e1, fe e2)
  | Annot (s, e)    -> Annot (s, fe e)
  in
  List.map
    (function
     | Def (x, ty, e, t) -> Def (fx x, ty, fe e, t)
     | Variable (x, e) -> Variable (fx x, fe e)
     | Inductive l ->
        Inductive (List.map (fun (x, y, e) -> (fx x, fx y, fe e)) l)
     | Withfrom (x, y, e) -> Withfrom (fx x, fx y, fe e)
     | Comment s -> Comment s
     | Command s -> Command s)


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
     | Def (x, _, e, _) -> use e; def x
     | Variable (x, e) -> use e; def x
     | Withfrom (x, y, e) -> use e; def x; def y
     | Comment _ | Command _ -> ()
     | Inductive l ->
        List.iter (fun (x, y, _) -> def x; def y) l;
        List.iter (fun (_, _, e) -> use e) l)
    instructions
  end;
  { defines = !defined;
    uses    = !used;
    tries   = !tried }


(** From cat-like instructions to coq-like instructions *)

let use_axioms = false

let transform_instrs force_defined (l : name instr list) : string instr list =
  let open StringSet in
  let ( ++ ) = union in
  let l = resolve_fresh l in
  let l = remove_withfrom l in
  let l = special_cases l in
  
  let infos = ref [] in
  let add_info s = infos := !infos @ [s] in
  
  let { uses; tries; _ } = naming_information l in
  let uses = of_list force_defined ++ uses in
  
  (* Informing user about undefined but try-with'ed names *)
  let ambiguous = elements (diff tries uses) in
  let warning =
    sprintf "The following set of variables is only used inside try/with's before
any definition:
  %s
the corresponding try/with's failed. Use the option -defined
id1,id2,... to make the corresponding ones succeed instead.
"
      (String.concat ", " ambiguous)
  in
  if ambiguous <> [] then add_info warning;

  (* Informing user about undefined names *)
  let ondemand = elements (diff uses (of_list (defined_in_prelude @ candidate_fields))) in
  let warning =
    ondemand
    |> String.concat ", "
    |> sprintf "The following set of variables is used but is neither defined in the
prelude nor provided by the candidate:
  %s
"
  in
  if ondemand <> [] then add_info warning;
  
  let provide = if use_axioms then unknown_axiom else unknown_def in
  let ondemand_definitions = List.map provide ondemand in
  let introduced_by_translation =
    of_list ["valid"; "witness_conditions"; "witness"; "relation_conditions"] in
  
  let fv = uses
           ++ of_list candidate_fields
           ++ of_list defined_in_prelude
           ++ of_list ondemand
           ++ introduced_by_translation
  in
  
  l
  |> resolve_shadowing add_info fv
  |> collect_conditions
  |> remove_trywith fv
  |> (@) ondemand_definitions
  |> fun l -> l @ [Comment ("Informations on the translation from cat to coq:\n\n"
                            ^ String.concat "\n" !infos ^ "\n")]
  |> resolve_charset


(** Print model in Coq syntax *)

let pprint_coq_model
      (verbosity : int)
      (notation : notation)
      (force_defined : string list)
      (prelude : string list)
      (parse_file : string -> AST.t)
      (model : AST.t) : string =
  let parse fname = let (_, _, i) = parse_file fname in i in
  let (_, name, instrs) = model in
  let intro_R_W_etc =
    if use_axioms
    then axioms
    else imports_candidate_fields
  in
  let verb lvl x = if verbosity >= lvl then x else [] in
  
  instrs

  (* We include stdlib.cat *)
  |> (fun is -> AST.Include (TxtLoc.none, "stdlib.cat") :: is)

  (* Including includes *)
  |> expand_include parse

  (* Remove unused definitions (at herd's syntax level) *)
  |> filter_unused_defs

  (* Simple line-by-line translation *)
  |> List.map (translate_instr notation) |> List.concat

  (* Core transformations *)
  (* TODO: maybe -- but only maybe -- some of those transformations
     would benefit from being done after elimination of unused *)
  |> transform_instrs force_defined
  
  (* Adding context: prelude, section, section definitions *)
  |> (fun instrs ->
    [
      (List.map (fun s -> Command s) prelude);
      [Command "Section Model."];
      (if notation = Cat then [Command "Open Scope cat_scope."] else []);
      start_definitions;
      intro_R_W_etc;
      middle_definitions;
      instrs;
      [Command "End Model."];
    ] |> List.concat)

  (* Remove unused definitions *)
  |> remove_unused ~keepalive:["events"; "witness_conditions"; "model_conditions"]

  (* Adding unfold hints *)
  |> (fun instrs ->
    let defined = filter_map (function Def (x, _, _, _) -> Some x | _ -> None) instrs in
    instrs @ verb 0 [Command (sprintf "\nHint Unfold %s : cat." (String.concat " " defined))])

  (* Add the definition of valid *)
  |> (fun is -> is @ [Command (end_text is)])

  (* Wrap up in comments *)
  |> (fun instrs ->
    verb 1 [Comment ("Translation of model " ^ name)] @
      instrs @
        verb 1 [Comment ("End of translation of model " ^ name)])

  (* Convert to a string *)
  |> List.map (pprint_instr verbosity)
  |> List.concat
  |> String.concat "\n"


(** Read commandline options *)

let allcats = ref false
let args = ref []
let cat = ref true
let convertfilename = ref false
let debug = ref false
let force_defined = ref []
let includes = ref []
let makefile = ref false
let notation = ref Cat
let output_file = ref None
let overwrite = ref false
let prelude = ref true
let quiet = ref false
let verbosity = ref 1
let yescat = ref false

let prog =
  if Array.length Sys.argv > 0 then
    Filename.basename Sys.argv.(0)
  else "cat2coq7"

let forbidden_chars = "-.+"

let usage =
  let s =
    (sprintf
       "Usage: %s [options]* <file.cat> [<file.cat>]*\n
        Translate .cat files into .v files, and create a Cat.v file
        containing basic definitions, including the one of candidate.\n"
       prog)
  in s (* keep this let for indentation *)

let options =
  [
    ("-allcats",
     Arg.Unit (fun () -> makefile := true; allcats := true),
     sprintf
       "
        add all the cats in herd's libdir's directory to the list of
        input files. Also turn on the -makefile option.  Use:
        %s -allcats && make -j7
        to check everything.\n"
       ("  " ^ prog))
  ;
    ("-convertfilename",
     Arg.Unit (fun () -> convertfilename := true),
     sprintf
       "
        do not read any file, simply display the filename converted
        to a coq-compatible filename (characters in \"%s\" are mapped
        to '_'). Note that the filenames are in the current directory,
        which may differ from the cat file(s) directory.\n"
       (String.escaped forbidden_chars)
    )
  ;
    ("-debug",
     Arg.Unit (fun () -> debug := true),
     sprintf
       "
        display which files are opened\n")
  ;
    ("-defined",
     Arg.String (fun s -> force_defined := split_on_char ',' s),
     sprintf
       "<ident1>[,<ident2>[,...]]
        make try..with succeed for these
        identifiers, even if they don't appear outside a try..with\n")
  ;
    ("-I",
     Arg.String (fun s -> includes := !includes @ [s]),
     sprintf
       "<dir>
        add <dir> to search path\n")
  ;
    ("-makefile",
     Arg.Unit (fun () -> makefile := true),
     sprintf
       "
        generate a Makefile for all the .v files generated, including
        Cat.v, and a file importeverything.v that check that all the
        validity conditions are defined.\n")
  ;
    ("-nocat",
     Arg.Unit (fun () -> cat := false),
     sprintf
       "
        do not write Cat.v\n")
  ;
    ("-notations",
     Arg.String (fun s -> try notation := List.assoc s notation_names
                          with Not_found -> failwith (sprintf "invalid notation: %s" s)),
     sprintf
       "%s
        notation system (default %s):
          none: define and use no notations
          cat:  define and use notations that look like .cat files
          kat:  import notations from the RelationAlgebra library\n"
       (String.concat "|" (List.map fst notation_names))
       (assoc_inv !notation notation_names)
    )
  ;
    ("-noprelude",
     Arg.Unit (fun () -> prelude := false),
     sprintf
       "
        do not include any prelude\n")
  ;
    ("-o",
     Arg.String (fun s -> output_file := Some s),
     sprintf
       "<filename>
        generated file name, - for standard output. The default is a
        coq-compatible name generated from the input filename. If this
        option is provided, only one file can be handled at a time.\n")
  ;
    ("-overwrite",
     Arg.Unit (fun () -> overwrite := true),
     sprintf
       "<filename>
        generated file name, - for standard output. The default is a
        coq-compatible name generated from the input filename. If this
        option is provided, only one file can be handled at a time.\n")
  ;
    ("-q",
     Arg.Unit (fun () -> quiet := true),
     sprintf
       "
        quiet: read and parse files but do not write anything\n")
  ;
    ("-v",
     Arg.Int (fun n -> verbosity := n),
     sprintf
       "<integer>
        verbosity level: more or less annotations in generated files.
        For now, can be either 0 and 1 (default 1)\n")
  ;
    ("-yescat",
     Arg.Unit (fun () -> yescat := true),
     sprintf
       "
        write Cat.v even if no .cat argument is given\n")
  ]

let () =
  Arg.parse
    options
    (fun s -> args := s :: !args)
    usage


let libfind =
  let module ML =
    MyLib.Make
      (struct
        let includes = !includes
        let env = Some "HERDLIB"
        let libdir = Filename.concat Version.libdir "herd"
        let debug = !debug
      end) in ML.find

module Parser =
  ParseModel.Make
    (struct
      let debug = false
      let libfind = libfind
    end)

let normalize_filename fname =
  let fname = Filename.basename fname in
  let fix_name =
    String.map
      (fun c -> if String.contains forbidden_chars c then '_' else c)
  in
  if Filename.check_suffix fname ".cat" then
    fix_name (Filename.chop_suffix fname ".cat")
  else
    invalid_arg "not a .cat file name, unsure what to convert"

let vfilename fname = normalize_filename fname ^ ".v"

let handle_filename fname prelude outchannel =
  let text =
    pprint_coq_model
      !verbosity
      !notation
      !force_defined
      prelude
      Parser.parse
      (Parser.parse fname)
  in
  match outchannel with
  | None -> ()
  | Some outchannel -> fprintf outchannel "%s\n" text


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

exception Return
let return () : unit = raise Return

let () =
  let current_filename = ref None in
  try
    if !convertfilename then
      !args
      |> List.map vfilename
      |> String.concat " "
      |> printf "%s\n"
      |> return;

    if !allcats then
      args :=
        !args @
          List.map (fun x -> x ^ ".cat")
          ["aarch64"; "aarch64fences"; "aarch64-obsolete"; "arm-alt"; "arm";
           "armfences"; "armllh"; "atom-arm"; "atom"; "c11_base"; "c11_cos";
           "c11_los"; "c11_orig"; "c11_partialSC"; "c11_simp"; "compat";
           "cos"; "coscat"; (* "cosllh"; "cos-opt"; *) "cross"; "doc64"; "fences";
           "filters"; "fulleieio"; "herd"; "herdcat"; "lessrelaxed"; "LL";
           "mini"; "minimal"; "minimalcat"; "mips"; "mipsfences";
           "mips-tso"; "naked"; "ppc"; "ppc-checks"; "ppcfences"; "ppo";
           "pretty"; "prettycat"; "qualcomm"; "rc11"; "riscv"; "riscv-defs";
           "riscv-total"; "sc2"; "sc"; "sccat"; "simple-arm"; "simple-c11";
           "stdlib"; "tso"; "uni"; "uniproc"; "uniproccat";
           "uniproc-normw-cat"; "uniproc+sca"; "x86fences"; "x86tso"];
    
    if !args = [] && not !yescat then
      printf "%s\n" usage
      |> return;

    let pre = if !prelude then read_file (libfind "prelude_cat2coq.v") else [] in

    let careful_open_out filename =
      if Sys.file_exists filename && not !overwrite then
        failwith (sprintf "File '%s' already exists. Use option \
                           -overwrite to ignore existing files."
                    filename)
      else
        (if !verbosity >= 2 then eprintf "Opening file for writing: %s\n" filename;
         open_out filename)
    in

    (* Output Cat.v file *)
    let () =
      if (!cat || !yescat) && !prelude then
        let o = careful_open_out "Cat.v" in
        List.iter (fprintf o "%s\n") pre
    in

    let trace fname = current_filename := Some fname; fname in
    let import = ["From Coq Require Import Relations String.";
                  "Require Import Cat."] in

    begin match !args, !quiet, !output_file with
    | [fname], false, Some "-" -> handle_filename (trace fname) import (Some stdout)
    | [fname], false, Some outfile -> handle_filename (trace fname) import (Some (careful_open_out outfile))
    | [fname], true, None -> handle_filename (trace fname) import None
    | _, true, Some _ -> failwith "options -o and -q are incompatible"
    | _, false, Some _ -> failwith "exactly one input file must be specified \
                                    if option -o is provided"
    | fnames, _, None ->
       List.iter
         (fun fname ->
           handle_filename (trace fname) import
             (if !quiet then None else Some (careful_open_out (vfilename fname))))
         fnames;

    if !makefile then begin
        let fnames = List.sort compare fnames in
        let files = List.map normalize_filename fnames in
        let v l = String.concat " " (List.map (fun x -> x ^ ".v") l) in

        let o = careful_open_out "importeverything.v" in
        fprintf o "Require Import Cat Relations.\n";
        fprintf o "Require %s.\n\n" (String.concat " " files);
        List.iter (fprintf o "Check %s.valid.\n") files;
        close_out o;

        let o = careful_open_out "Makefile" in
        fprintf o "
cat_vs=%s

cat_vos=$(cat_vs:=o)

all_vos=$(cat_vos) Cat.vo importeverything.vo

all: $(all_vos)
importeverything.vo: $(cat_vos)
$(cat_vos): Cat.vo

%%.vo: %%.v
	coqc $<
clean:
	rm -f $(all_vos) $(all_vos:vo=glob)
"
          (v files);
      end;
    end
    
  with
  | Misc.Fatal errmsg
    | Failure errmsg ->
     eprintf "Error%s: %s\n"
       (match !current_filename with
        | None -> ""
        | Some n -> sprintf "(%s)" n)
       errmsg;
     exit 1
  | Return -> ()
