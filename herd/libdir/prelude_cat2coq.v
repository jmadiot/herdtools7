(* Start of prelude for coq translation of .cat files *)
From Coq Require Import Ensembles Relations List.

Definition set := Ensemble.
Definition rln := relation.

Class SetLike A :=
  { union : A -> A -> A;
    intersection : A -> A -> A;
    diff : A -> A -> A;
    universal : A;
    incl : A -> A -> Prop}.

Definition complement {A} `{SetLike A} (x : A) := diff universal x.
Definition empty {A} `{SetLike A} : A := diff universal universal.
Definition is_empty {A} `{SetLike A} (x : A) : Prop := incl x (diff universal universal).

Instance SetLike_set (A : Type) : SetLike (set A) :=
  {| union := Union A;
     intersection := Intersection A;
     diff := Setminus A;
     universal := Full_set A;
     incl := Included A |}.

Instance SetLike_rln (A : Type) : SetLike (rln A) :=
  {| union := Relation_Operators.union A;
     intersection := fun R S x y => R x y /\ S x y;
     diff := fun R S x y => R x y /\ ~S x y;
     universal := fun x y => True;
     incl := fun R S => forall x y, R x y -> S x y |}.

Definition rln_comp {A} : rln A -> rln A -> rln A := fun R S => fun x z => exists y, R x y /\ S y z.

Definition rln_mirror {A} : rln A -> rln A := fun R => fun x y => R y x.

Definition cartesian {A} : set A -> set A -> rln A := fun X Y x y => X x /\ Y y.

Definition id {A} : rln A := eq.

Definition domain {A} : rln A -> set A := fun R x => exists y, R x y.

Definition range {A} : rln A -> set A := fun R y => exists x, R x y.

Definition irreflexive {A} (R : rln A) := forall x, ~R x x.

Definition acyclic {A} (R : rln A) := irreflexive (clos_trans A R).

Definition total_order {A} (R : rln A) := order A R /\ forall x y, R x y \/ R y x.

Definition linearisations {A} (X : set A) (R : rln A) : set (rln A) :=
  fun S => total_order S /\ incl R S.

Definition set_flatten {A} : set (set A) -> set A := fun xss x => exists xs, xss xs /\ xs x.

Definition map {A B} (f : A -> B) (X : set A) : set B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : rln A) (wss : set (set A)) : set (set (rln A)) :=
  map (fun ws => linearisations ws pco) wss.

Definition cross {A} (Si : set (set (rln A))) : set (rln A) :=
  fun ei : rln A => exists (l : list (rln A)) (L : list (set (rln A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : set A -> rln A := fun X x y => X x /\ x = y.

Class HaveSingleton A B := { singleton : A -> B }.

Instance HaveSingleton_set A : HaveSingleton A (set A) :=
  { singleton := Singleton A }.

Instance HaveSingleton_rln A : HaveSingleton (A * A) (rln A) :=
  { singleton := fun xy x y => xy = (x, y) }.

Definition add_element {A B} `{SetLike B} `{HaveSingleton A B} : A -> B -> B :=
  fun x X => union (singleton x) X.


Declare Scope cat_scope.
Delimit Scope cat_scope with cat.

Infix "|" := union        (at level 70, right associativity) : cat_scope.
Infix "++":= add_element  (at level 60, right associativity) : cat_scope.
Infix ";" := rln_comp     (at level 55, right associativity) : cat_scope.
Infix "&" := intersection (at level 51, right associativity) : cat_scope.
Infix "\" := diff         (at level 45, left associativity) : cat_scope.
Infix "*" := cartesian    (at level 40, left associativity) : cat_scope.

(* Caution: not the same precedence as in cat for ~ *)
Notation "~ x" := (complement x) (at level 75, right associativity) : cat_scope.
Notation " [ x ] " := (diagonal x).
Notation " x ^-1 " := (rln_mirror x)        (at level 30, no associativity).
Notation " x ^+ "  := (clos_trans _ x)      (at level 30, no associativity).
Notation " x ^* "  := (clos_refl_trans _ x) (at level 30, no associativity).
Notation " x ? "   := (clos_refl _ x)       (at level 30, no associativity).

Axiom events : Set.

(* Makes possible to default to events when A cannot be inferred *)
Instance SetLike_set_events : SetLike (set events) := SetLike_set events.
Instance SetLike_rln_events : SetLike (rln events) := SetLike_rln events.

(* Pre-defined event sets from the documentation *)
Definition emptyset : set events := empty. (* empty set of events *)
Axiom W   : set events.    (* write events *)
Axiom R   : set events.    (* read events *)
Definition M := union R W. (* memory events  // we have M = W ∪ R *)
Axiom IW  : set events.    (* initial writes // feed reads that read from the initial state *)
Axiom FW  : set events.    (* final writes   // writes that are observed at the end of test execution *)
Axiom B   : set events.    (* branch events *)
Axiom RMW : set events.    (* read-modify-write events *)
Axiom F   : set events.    (* ↑fence events *)

Axiom loc : rln events.

Definition classes_loc (S : set events) : set (set events) :=
  fun Si => forall x y, Si x -> Si y -> loc x y.

Definition to_id : set events -> rln events := fun X x y => X x /\ x = y.

(** End of prelude *)
