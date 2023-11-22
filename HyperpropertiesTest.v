From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Hyperproperties Require Import Hyperproperties.

Inductive State : Type :=
  | BottomState : State.

Module BottomStateMod <: StateTypeMod.
  Definition StateType := State.
End BottomStateMod.

Module CrashHyperMod := Hyperproperty BottomStateMod.
Import CrashHyperMod.

CoFixpoint halt_trace : psi_inf := Cons BottomState halt_trace.
Example empty_system : system := Singleton trace halt_trace.

(* An example property which describes the empty program. *)
Example crash_property : property := Singleton trace halt_trace.
Check crash_property.
Example crash_hyperproperty : hyperproperty :=
  Add system (Singleton system empty_system) (Singleton trace halt_trace).

Lemma crash_property_in_PROP : In property PROP crash_property.
Proof. constructor. Qed.

Lemma crash_hyperproperty_in_HP : In hyperproperty HP crash_hyperproperty.
Proof. constructor. Qed.

Lemma empty_system_satisfies_crash_property :
  satisfies_property empty_system crash_property.
Proof. intros x H. inversion H. constructor. Qed.

Lemma empty_system_satisfies_crash_hyperproperty :
  satisfies_hyperproperty empty_system crash_hyperproperty.
Proof. constructor. apply In_singleton. Qed.

Lemma crash_system_satisfies_crash_property :
  satisfies_property empty_system crash_property.
Proof. intros t H. apply H. Qed.

Lemma crash_system_satisfies_crash_hyperproperty :
  satisfies_hyperproperty empty_system crash_hyperproperty.
Proof. apply Union_intror. apply In_singleton. Qed.
(* TODO(ptcrews): Complete proof. *)
Lemma crash_property_lifts_to_crash_hyperproperty :
  Same_set system [[crash_property]] crash_hyperproperty.
Proof.
  split; intros p H.
Admitted.

Lemma bottom_state_prefix_crash_trace :
  prefix halt_trace [BottomState].
Proof.
  rewrite (unfold_Stream halt_trace). repeat constructor.
Qed.

Example bottom_state_set : Ensemble subtrace :=
  Singleton subtrace [BottomState].

Example halt_trace_set : Ensemble trace :=
  Singleton trace halt_trace.

Lemma bottom_state_set_prefix_crash_hyperproperty :
  prefix_set halt_trace_set bottom_state_set.
Proof.
  intros t' H. exists halt_trace. split.
  - unfold In. unfold halt_trace_set. apply In_singleton.
  - unfold bottom_state_set in H. destruct t'.
    + inversion H.
    + inversion H. apply bottom_state_prefix_crash_trace.
Qed.
