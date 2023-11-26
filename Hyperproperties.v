From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Sets.Finite_sets.
From Coq Require Import Sets.Constructive_sets.

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

Definition satisfies_property (s : system) (P : property) :=
  Included trace s P.
Definition satisfies_hyperproperty (s : system) (Hp : hyperproperty) :=
  In system Hp s.

Lemma Rewrite_Included_satisfies_property : forall (s : system) (P : property),
  Included trace s P = satisfies_property s P.
Proof. reflexivity. Qed.

Lemma Rewrite_In_satisfies_hyperproperty : forall (s : system) (Hp : hyperproperty),
  In system Hp s = satisfies_hyperproperty s Hp.
Proof. reflexivity. Qed.

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
  forall (p : subtrace),
  In (subtrace) prefixes p -> exists (t: trace), In (trace) traces t /\ prefix t p.

(* Definition Obs :=  Full_set (Ensemble subtrace). *)
Definition Obs := Ensemble subtrace.

Definition safety_property (p: property) :=
  forall (t : trace),
  ~ In (trace) p t -> exists (m : subtrace), forall (t' : trace), prefix t m
                      /\ (prefix t' m -> ~ In (trace) p t').

Definition safety_hyperproperty (hp: hyperproperty) :=
  forall (s : system),
  ~ In (system) hp s -> exists (m : Obs), forall (s': system), prefix_set s m
                        /\  (prefix_set s' m -> ~ In (system) hp s').

(* The set of all Safety Properties *)
Definition SP := { p:property | safety_property p}.

(* The set of all Safety Hyperproperties *)
Definition SHP := { h:hyperproperty | safety_hyperproperty h}.

Lemma not_included_gives_exists : forall (p : property) (s : system),
  ~ Included trace s p -> exists t : trace, ~ In trace p t /\ In trace s t.
Proof. Admitted.

Theorem lifting_preserves_safety:
  forall (p : property), safety_property p <-> safety_hyperproperty [[p]].
Proof.
  intros p. split; intros H.
  - intros s H'. rewrite Rewrite_In_satisfies_hyperproperty in *.
    rewrite <- lifting_preserves_satisfiability in *.
    unfold satisfies_property in H'. unfold not in *.
    unfold safety_property in H.
    apply not_included_gives_exists in H'. destruct H' as [t H'']. destruct H'' as [Hp Hs].
    specialize (H t). apply H in Hp. destruct Hp as [m Hp'].
    exists (Singleton subtrace m). intros s'. split.
    + unfold prefix_set. intros p' H0. apply Singleton_inv in H0. rewrite H0 in *.
      exists t. split.
      ++ apply Hs.
      ++ destruct (Hp' t). apply H1.
    + intros Hpset. rewrite Rewrite_In_satisfies_hyperproperty.
      rewrite <- lifting_preserves_satisfiability.
      unfold satisfies_property. unfold prefix_set in Hpset. destruct (Hpset m).
      ++ apply In_singleton.
      ++ intros contra. unfold Included in contra. specialize (contra x). destruct H0 as [H0 H0'].
         apply contra in H0. specialize (Hp' x). destruct Hp' as [Hp' Hp''].
         apply Hp'' in H0'. contradiction.
  - admit.
Admitted.

End Hyperproperty.
