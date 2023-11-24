From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Sets.Finite_sets. 

Module Type StateTypeMod.
  Parameter StateType: Type.
  (* TODO(ptcrews): We probably need equality axioms here *)
End StateTypeMod.

Module Hyperproperty (SM: (StateTypeMod)).
Import SM.

Definition trace := Stream StateType.
Definition subtrace := list StateType.

Definition psi_fin := subtrace.
Definition psi_inf := trace.

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

Lemma lifting_preserves_satisfiability:
  forall (s : system) (P : property),
  satisfies_property s P <-> satisfies_hyperproperty s [[P]].
Proof.
  intros s P. split; intros H.
  - apply Definition_of_Power_set. apply H.
  - inversion H. apply H0.
Qed.

Inductive prefix : trace -> subtrace -> Prop :=
  | prefix_nil (t : trace) : prefix t nil
  | prefix_cons (s : StateType) (t : trace) (t' : subtrace) (H : prefix t t')
      : prefix (Cons s t) (s :: t').

Definition prefix_set
  (traces : Ensemble trace)
  (prefixes : Ensemble subtrace) :=
  forall (t' : subtrace), In (subtrace) prefixes t' ->
  (exists (t : trace), In (trace) traces t /\ prefix t t').

Definition safety_property (p: property) :=
forall (t:trace), forall (t':trace), exists (m:subtrace), ~ In (trace) p t -> 
( prefix t m /\ ( prefix t' m -> ~ In (trace) p t')) . 

Definition SP := { p:property | safety_property p}.

Definition Obs :=  Full_set (Ensemble subtrace).

(* fix this to be systems not properties *)
Definition safety_hyperproperty (h: hyperproperty) := 
forall (s:system), ( forall (s':system), (exists (M: Ensemble subtrace), ~ In (system) h s -> 
 In (Ensemble subtrace) Obs M /\ prefix_set s M
/\  prefix_set s' M -> ~ In (property) h s') ).

Definition SHP := { h:hyperproperty | safety_hyperproperty h}.

Lemma lifting_preserves_safety:
  forall (p:property), safety_property p <-> safety_hyperproperty [[p]].
Proof.
  intros p. split; intros H.
  - unfold safety_hyperproperty. unfold safety_property in H. intros T. intros T'. admit. 
  - unfold safety_property. unfold safety_hyperproperty in H. intros t'. intros t.  admit. 
  Admitted.

End Hyperproperty.
