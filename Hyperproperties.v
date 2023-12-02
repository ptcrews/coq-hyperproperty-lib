From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Sets.Finite_sets.
From Coq Require Import Sets.Constructive_sets.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Logic.Classical_Pred_Type.


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
Proof. intros p s H. unfold Included in H. apply not_all_ex_not in H. destruct H.
exists x.  apply imply_to_and   in H. destruct H. split.
+ apply H0.
+ apply H.
Qed. 

Lemma inhabited_gives_exists: forall (U: Type) (A:Ensemble U),
  Inhabited U A -> exists x : U, In U A x.
Proof. Admitted.

Lemma prefix_set_Singleton : forall (t : trace) (prefixes : Ensemble subtrace),
  Inhabited subtrace prefixes /\ prefix_set (Singleton trace t) prefixes ->
  exists p : subtrace, In subtrace prefixes p /\
  (forall t' : trace, prefix t' p -> prefix_set (Singleton trace t') prefixes).
intros t prefixes.
Proof. Admitted.



Theorem lifting_preserves_safety:
  forall (p : property), safety_property p <-> safety_hyperproperty [[p]].
Proof.
  intros p. split; intros H.
  - intros s H'. rewrite Rewrite_In_satisfies_hyperproperty in *.
    rewrite <- lifting_preserves_satisfiability in *.
    unfold satisfies_property in H'. unfold not in *.
    unfold safety_property in H.
    apply not_included_gives_exists in H'. destruct H' as [t H''].
    destruct H'' as [Hp Hs].
    specialize (H t). apply H in Hp. destruct Hp as [m Hp'].
    exists (Singleton subtrace m). intros s'. split.
    + unfold prefix_set. intros p' H0. apply Singleton_inv in H0.
      rewrite H0 in *. exists t. split.
      ++ apply Hs.
      ++ destruct (Hp' t). apply H1.
    + intros Hpset. rewrite Rewrite_In_satisfies_hyperproperty.
      rewrite <- lifting_preserves_satisfiability.
      unfold satisfies_property. unfold prefix_set in Hpset. destruct (Hpset m).
      ++ apply In_singleton.
      ++ intros contra. unfold Included in contra. specialize (contra x).
         destruct H0 as [H0 H0'].
         apply contra in H0. specialize (Hp' x). destruct Hp' as [Hp' Hp''].
         apply Hp'' in H0'. contradiction.
  - intros t H'. unfold safety_hyperproperty in H.
    destruct (H (Singleton trace t)).
    + intros contra. rewrite Rewrite_In_satisfies_hyperproperty in contra.
      rewrite <- lifting_preserves_satisfiability in contra.
      unfold satisfies_property in contra.
      unfold not in H'. unfold Included in contra. specialize (contra t).
      apply H' in contra.
      ++ apply contra.
      ++ apply In_singleton.
    + assert (Hinhabited: Inhabited subtrace x
                          /\ prefix_set (Singleton trace t) x). {
        destruct (H0 (Singleton trace t)) as [H0' H0''].
        split.
        - apply H0'' in H0'. apply NNPP. unfold not. intros.
          destruct (H0 p) as [H2 H2']. destruct H2'.
          + unfold prefix_set. intros. apply Inhabited_intro in H3.
            apply H1 in H3. contradiction.
          + unfold lift. unfold In. apply Definition_of_Power_set.
            unfold Included. intros. apply H3.
        - apply H0'.
      }
      apply prefix_set_Singleton in Hinhabited.
      destruct Hinhabited as [x' Hinhabited].
      destruct Hinhabited as [Hinhabited Hprefix_set].
      exists x'. intros t'. split.
      ++ destruct (H0 (Singleton trace t')) as [Ht' _].
         specialize (Ht' x'). apply Ht' in Hinhabited.
         destruct Hinhabited as [t0 Hinhabited _].
         destruct Hinhabited. apply Singleton_inv in H1. rewrite H1 in *.
         apply H2.
      ++ intros Hprefix. destruct (H0 (Singleton trace t')) as [_ Ht'].
         rewrite Rewrite_In_satisfies_hyperproperty in Ht'.
         rewrite <- lifting_preserves_satisfiability in Ht'.
         rewrite <- Rewrite_Included_satisfies_property in Ht'.
         intros contra.
         destruct Ht'.
         +++ apply Hprefix_set. apply Hprefix.
         +++ unfold Included. intros. apply Singleton_inv in H1. subst x0.
             apply contra.
Qed.

End Hyperproperty.
