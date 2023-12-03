From Coq Require Import Arith.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Sets.Finite_sets.
From Coq Require Import Sets.Constructive_sets.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Logic.Classical_Pred_Type.
From Coq Require Import Lists.ListSet.
From Coq Require Import Structures.Equalities.
Scheme Equality for list.

Module Type StateTypeMod.
  Parameter StateType: Type.
  (* TODO(ptcrews): We probably need equality axioms here *)
  Parameter eq_dec: forall x y: StateType, {x = y} + {x <> y}.
  Parameter eqb: StateType -> StateType -> bool.
  Parameter eqb_eq: forall x y: StateType, eqb x y = true <-> x = y.
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
  Ensembles.In system Hp s = satisfies_hyperproperty s Hp.
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
  (prefixes : set subtrace) :=
  forall (p : subtrace),
  set_In p prefixes -> exists (t: trace), In (trace) traces t /\ prefix t p.

(* Definition Obs :=  Full_set (Ensemble subtrace). *)
Definition Obs := set subtrace.

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

Fixpoint max_prefix (prefix: set subtrace) : option subtrace :=
  match prefix with
  | nil => None
  | p :: prefix =>
      match max_prefix prefix with
      | None => Some p
      | Some p' => if (length p) <=? (length p') then Some p' else Some p
      end
  end.

Lemma non_empty_gives_max_prefix: forall (prefixes : set subtrace),
  prefixes <> (empty_set subtrace) ->
  exists p: subtrace, max_prefix prefixes = Some p.
Proof.
  intros. destruct prefixes.
  - contradiction.
  - destruct (max_prefix (s::prefixes)) eqn:H'.
    + exists s0. reflexivity.
    + inversion H'. destruct (max_prefix prefixes).
      ++ destruct (length s <=? length s0); inversion H1.
      ++ inversion H1.
Qed.

Lemma max_prefix_gives_element: forall (prefixes: set subtrace) (p: subtrace),
  max_prefix prefixes = Some p -> set_In p prefixes.
Proof.
  intros. induction prefixes.
  - inversion H.
  - destruct (list_eq_dec _ eqb) with p a as [H1|H2]; try apply eqb_eq.
    + rewrite H1 in *. simpl. left. reflexivity.
    + simpl. right. apply IHprefixes. simpl in H.
      assert (Hneq: Some a <> Some p). { congruence. }
      destruct (max_prefix prefixes).
      ++ destruct (length a <=? length s).
         +++ apply H.
         +++ contradiction.
      ++ contradiction.
Qed.

Lemma prefix_set_Singleton : forall (t : trace) (prefixes : set subtrace),
  prefixes <> (empty_set subtrace) /\ prefix_set (Singleton trace t) prefixes ->
  exists p : subtrace, set_In p prefixes /\
  (forall t' : trace, prefix t' p -> prefix_set (Singleton trace t') prefixes).
Proof.
intros t prefixes H. destruct H as [H H']. unfold prefix_set in H'.
apply non_empty_gives_max_prefix in H. destruct H as [p H1]. exists p.
split.
- apply max_prefix_gives_element. apply H1.
- intros. unfold prefix_set. intros. exists t'. split.
  + apply In_singleton.
  + admit.
Admitted.

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
    exists [m]. intros s'. split.
    + unfold prefix_set. intros p' H0. inversion H0.
      rewrite H1 in *. exists t. split.
      ++ apply Hs.
      ++ destruct (Hp' t). apply H2.
      ++ inversion H1.
    + intros Hpset. rewrite Rewrite_In_satisfies_hyperproperty.
      rewrite <- lifting_preserves_satisfiability.
      unfold satisfies_property. unfold prefix_set in Hpset. destruct (Hpset m).
      ++ simpl. left. reflexivity.
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
    + assert (Hinhabited: x <> empty_set subtrace
                          /\ prefix_set (Singleton trace t) x). {
        destruct (H0 (Singleton trace t)) as [H0' H0''].
        split.
        - apply H0'' in H0'. apply NNPP. unfold not. intros.
          destruct (H0 p) as [H2 H2']. destruct H2'.
          + unfold prefix_set. intros. apply NNPP in H1. rewrite H1 in H3. inversion H3.
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
