Module Hyperproperty.

From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.

Variable program_state : Type.
Variable dummy_state : program_state.

Inductive state : Type :=
  | BottomState : state
  | ProgramState : program_state -> state.

Definition trace := Stream state.
Definition subtrace := list state.

Definition psi_fin := subtrace.
Definition psi_inf := trace.

CoFixpoint halt_trace : psi_inf := Cons BottomState halt_trace.

(* TODO(ptcrews): Do we want these to type check as psi_inf? *)
Definition system := Ensemble trace.
Definition property := Ensemble trace.
Definition hyperproperty := Ensemble system.

Definition PROP := Full_set property.
Definition HP := Full_set hyperproperty.

Definition satisfies_property (S : system) (P : property) :=
  Included trace S P.
Definition satisfies_hyperproperty (S : system) (Hp : hyperproperty) :=
  In system Hp S.

Definition lift (P : property) : hyperproperty := Power_set trace P.

Notation "[[ P ]]" := (lift P).

Inductive prefix : trace -> subtrace -> Prop :=
  | prefix_nil (t : trace) : prefix t nil
  | prefix_cons (s : state) (t : trace) (t' : subtrace) (H : prefix t t')
      : prefix (Cons s t) (s :: t').

Definition prefix_set
  (traces : Ensemble trace)
  (prefixes : Ensemble subtrace) :=
  forall (t' : subtrace), In (subtrace) prefixes t' ->
  (exists (t : trace), In (trace) traces t /\ prefix t t').

End Hyperproperty.
