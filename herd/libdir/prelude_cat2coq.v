(* Start of prelude for coq translation of .cat files *)
From Coq Require Import Ensembles Relations RelationClasses List String.

Definition set := Ensemble.

Class SetLike A :=
  { union : A -> A -> A;
    intersection : A -> A -> A;
    diff : A -> A -> A;
    universal : A;
    incl : A -> A -> Prop }.

Instance SetLike_set (A : Type) : SetLike (set A) :=
  {| union := Union A;
     intersection := Intersection A;
     diff := Setminus A;
     universal := Full_set A;
     incl := Included A |}.

Instance SetLike_relation (A : Type) : SetLike (relation A) :=
  {| union := Relation_Operators.union A;
     intersection := fun R S x y => R x y /\ S x y;
     diff := fun R S x y => R x y /\ ~S x y;
     universal := fun x y => True;
     incl := fun R S => forall x y, R x y -> S x y |}.

Definition complement {A} `{SetLike A} (x : A) := diff universal x.

Definition empty {A} `{SetLike A} : A := diff universal universal.

Definition is_empty {A} `{SetLike A} (x : A) : Prop := incl x (diff universal universal).

Definition rel_seq {A} : relation A -> relation A -> relation A := fun R S => fun x z => exists y, R x y /\ S y z.

Definition rel_inv {A} : relation A -> relation A := fun R => fun x y => R y x.

Definition cartesian {A} : set A -> set A -> relation A := fun X Y x y => X x /\ Y y.

Definition id {A} : relation A := eq.

Definition domain {A} : relation A -> set A := fun R x => exists y, R x y.

Definition range {A} : relation A -> set A := fun R y => exists x, R x y.

Definition irreflexive {A} (R : relation A) := forall x, ~R x x.

Definition acyclic {A} (R : relation A) := irreflexive (clos_trans A R).

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Definition linearisations {A} (X : set A) (R : relation A) : set (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition set_flatten {A} : set (set A) -> set A := fun xss x => exists xs, xss xs /\ xs x.

Definition map {A B} (f : A -> B) (X : set A) : set B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : relation A) (wss : set (set A)) : set (set (relation A)) :=
  map (fun ws => linearisations ws pco) wss.

Definition cross {A} (Si : set (set (relation A))) : set (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (set (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : set A -> relation A := fun X x y => X x /\ x = y.

Class HasSingleton A B := { singleton : A -> B }.

Instance HasSingleton_set A : HasSingleton A (set A) :=
  { singleton := Singleton A }.

Instance HasSingleton_relation A : HasSingleton (A * A) (relation A) :=
  { singleton := fun xy x y => xy = (x, y) }.

Definition add_element {A B} `{SetLike B} `{HasSingleton A B} : A -> B -> B :=
  fun x X => union (singleton x) X.


Declare Scope cat_scope.
Delimit Scope cat_scope with cat.

Infix "∪" := union        (at level 70, right associativity) : cat_scope.
Infix "++":= add_element  (at level 60, right associativity) : cat_scope.
Infix ";;" := rel_seq     (at level 55, right associativity) : cat_scope.
Infix "&" := intersection (at level 51, right associativity) : cat_scope.
Infix "\" := diff         (at level 45, left associativity)  : cat_scope.
Infix "*" := cartesian    (at level 40, left associativity)  : cat_scope.

(* Caution: not the same precedence as in cat for ~ *)
Notation "~ x" := (complement x) (at level 75, right associativity)         : cat_scope.
Notation " [ x ] " := (diagonal x)                                          : cat_scope.
Notation " x ^-1 " := (rel_inv x)           (at level 30, no associativity) : cat_scope.
Notation " x ^+ "  := (clos_trans _ x)      (at level 30, no associativity) : cat_scope.
Notation " x ^* "  := (clos_refl_trans _ x) (at level 30, no associativity) : cat_scope.
Notation " x ? "   := (clos_refl _ x)       (at level 30, no associativity) : cat_scope.

(* Execution given as an argument to the model *)

Record execution :=
  {
    events : Set;
    R   : set events; (* write events *)
    W   : set events; (* read events *)
    IW  : set events; (* initial writes *)
    FW  : set events; (* final writes *)
    B   : set events; (* branch events *)
    RMW : set events; (* read-modify-write events *)
    F   : set events; (* fence events *)
    po  : relation events; (* order of instructions in thread *)
    rf  : relation events; (* read from *)
    co  : relation events; (* coherence order, aka
                                mo (memory order), aka
                                ws (write serialization) *)
    int : relation events; (* events occuring in the same thread *)
    ext : relation events; (* events occuring in different threads *)
    loc : relation events; (* events occuring on the same location *)
    addr: relation events; (* address dependence *)
    data: relation events; (* data dependence *)
    ctrl: relation events; (* ctrl dependence *)
    unknown_set : string -> set events;
    unknown_relation : string -> relation events;
  }.

(** End of prelude *)
