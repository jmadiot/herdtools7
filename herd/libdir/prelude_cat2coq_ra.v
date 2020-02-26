(** Start of prelude for coq translation of .cat files *)
From Coq Require Import Ensembles List String RelationClasses.
(** This prelude uses definitions from RelationAlgebra *)
From RelationAlgebra Require Import all.

Definition set := dset.
Definition relation A := hrel A A.

Class SetLike A :=
  { union : A -> A -> A;
    intersection : A -> A -> A;
    diff : A -> A -> A;
    universal : A;
    incl : A -> A -> Prop }.

Instance SetLike_set (A : Type) : SetLike (dset A) :=
  {| union := fun X Y a => orb (X a) (Y a);
     intersection := fun X Y a => andb (X a) (Y a);
     diff := fun X Y a => andb (Y a) (negb (Y a));
     universal := fun _ => true;
     incl := fun X Y => forall a, X a = true -> Y a = true |}.

Instance SetLike_relation (A : Type) : SetLike (relation A) :=
  {| union := cup;
     intersection := cap;
     diff := fun R S => cap R (neg S);
     universal := top;
     incl := leq |}.

Definition complement {A} `{SetLike A} (x : A) := diff universal x.

Definition empty {A} `{SetLike A} : A := diff universal universal.

Definition is_empty {A} `{SetLike A} (x : A) : Prop := incl x (diff universal universal).

Definition rel_seq {A} : relation A -> relation A -> relation A := dot A A A.

Definition rel_inv {A} : relation A -> relation A := cnv A A.

Definition cartesian {A} : dset A -> dset A -> relation A := fun X Y x y => X x /\ Y y.

Definition id {A} : relation A := eq.

Axiom all_dec : forall (X : Prop), { X } + { ~X }.
Definition bool_of_prop (X : Prop) := if all_dec X then true else false.
Definition domain {A} : relation A -> dset A := fun R x => bool_of_prop (exists y, R x y).

Definition range {A} : relation A -> dset A := fun R y => bool_of_prop (exists x, R x y).

Definition irreflexive {A} (R : relation A) := forall x, ~R x x.

Notation refl_clos := (fun R => union R id) (only parsing).

Notation trans_clos := (hrel_str _) (only parsing).

Notation refl_trans_clos := (hrel_itr _) (only parsing).

Definition acyclic {A} (R : relation A) := incl (intersection (trans_clos R) id) empty.

Class StrictTotalOrder {A} (R : relation A) :=
  { StrictTotalOrder_Strict :> StrictOrder R;
    StrictTotalOrder_Total : forall a b, a <> b -> (R a b \/ R b a) }.

Definition linearisations {A} (X : Ensemble A) (R : relation A) : Ensemble (relation A) :=
  fun S => StrictTotalOrder S /\ incl R S.

Definition set_flatten {A} : Ensemble (Ensemble A) -> Ensemble A := fun xss x => exists xs, xss xs /\ xs x.

Definition map {A B} (f : A -> B) (X : Ensemble A) : Ensemble B := fun y => exists x, X x /\ y = f x.

Definition co_locs {A} (pco : relation A) (wss : Ensemble (Ensemble A)) : Ensemble (Ensemble (relation A)) :=
  map (fun ws => linearisations ws pco) wss.

Definition cross {A} (Si : Ensemble (Ensemble (relation A))) : Ensemble (relation A) :=
  fun ei : relation A => exists (l : list (relation A)) (L : list (Ensemble (relation A))),
      (forall x y, ei x y <-> exists e, In e l /\ e x y) /\
      (forall X, Si X <-> In X L) /\
      Forall2 (fun ei Si => Si ei) l L.

Definition diagonal {A} : dset A -> relation A := fun X x y => X x /\ x = y.

Declare Scope cat_scope.

(* Execution given as an argument to the model *)

Record candidate :=
  {
    (* Documentation for names:
       http://diy.inria.fr/doc/herd.html#language:identifier *)
    events : Set;
    W   : dset events; (* read events *)
    R   : dset events; (* write events *)
    IW  : dset events; (* initial writes *)
    FW  : dset events; (* final writes *)
    B   : dset events; (* branch events *)
    RMW : dset events; (* read-modify-write events *)
    F   : dset events; (* fence events *)

    po  : relation events; (* program order *)
    addr: relation events; (* address dependency *)
    data: relation events; (* data dependency *)
    ctrl: relation events; (* control dependency *)
    rmw : relation events; (* read-exclusive write-exclusive pair *)
    amo : relation events; (* atomic modify *)

    rf  : relation events; (* read-from *)
    loc : relation events; (* same location *)
    ext : relation events; (* external *)
    int : relation events; (* internal *)

    (* Two functions for unknown sets or relations that are found in
    .cat files. cat2coq uses [unknown_set "ACQ"] when translating
    some parts of cat files about C11 *)
    unknown_set : string -> dset events;
    unknown_relation : string -> relation events;
  }.

Hint Unfold events W R IW FW B RMW F po addr data ctrl rmw amo rf loc ext int unknown_set unknown_relation : cat_record.
Hint Unfold union intersection diff universal incl SetLike_set SetLike_relation rel_seq rel_inv : cat_defs.

(** End of prelude *)
