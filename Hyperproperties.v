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

Fixpoint max_prefix (prefix: set subtrace) : subtrace :=
  match prefix with
  | nil => []
  | p :: prefix =>
      let p' := max_prefix prefix in
        if (length p') <=? (length p) then p else p'
  end.

Lemma non_empty_gives_element: forall (prefixes: set subtrace) (p: subtrace),
  prefixes <> empty_set subtrace -> set_In (max_prefix prefixes) prefixes.
Proof.
  intros prefixes. induction prefixes.
  - intros. unfold empty_set in H. contradiction.
  - intros. simpl. destruct (length (max_prefix prefixes) <=? length a) eqn:Hsz.
    + left. reflexivity.
    + destruct prefixes.
      ++ inversion Hsz.
      ++ right. apply IHprefixes. apply p. unfold empty_set. unfold not. intros.
         inversion H0.
Qed.

Lemma max_prefix_longest_element: forall (prefixes: set subtrace) (p p': subtrace),
  set_In p' prefixes -> length p' <= length (max_prefix prefixes).
Proof.
  intros prefixes. induction prefixes.
  - intros. inversion H.
  - intros. simpl. destruct (length (max_prefix prefixes) <=? length a) eqn:Hlen.
    + apply leb_complete in Hlen. inversion H.
      ++ subst a. apply Nat.le_refl.
      ++ apply Nat.le_trans with (m:=(length (max_prefix prefixes))).
         apply IHprefixes. apply p. apply H0. apply Hlen.
    + apply Nat.leb_gt in Hlen. inversion H. 
      ++ subst a. apply Nat.lt_le_incl. apply Hlen.
      ++ apply IHprefixes. apply p. apply H0.
Qed.

Lemma list_head_iff: forall (p p': subtrace) (a: StateType),
  a::p = a::p' <-> p = p'.
Proof.
  intros. split.
  - intros. generalize dependent p'. induction p.
    + intros. injection H. intros. apply H0.
    + intros. destruct p'.
      ++ injection H. intros. inversion H0.
      ++ destruct (eqb a0 s) eqn:Heqb; injection H; intros; subst s; f_equal; apply H0.
  - intros. generalize dependent p'. induction p.
    + intros. rewrite H. reflexivity.
    + intros. f_equal. apply H.
Qed.

Lemma prefix_is_iterative: forall (t: trace) (p p': subtrace),
  prefix t (p ++ p') -> prefix t p.
Proof.
  intros. generalize dependent t. induction p.
  - intros. apply prefix_nil.
  - intros. inversion H. subst s t' t. apply prefix_cons. apply IHp. apply H2.
Qed.

Lemma firstn_equal_longest_prefix: forall (t: trace) (p p': subtrace),
  prefix t p /\ prefix t p' /\ length p' <= length p -> firstn (length p') p = p'.
Proof.
  intros t p p' [H0 [H1 H2] ]. generalize dependent p. generalize dependent t.
  induction p'.
  - intros. simpl. reflexivity.
  - intros. simpl. destruct p.
    + inversion H2.
    + destruct t. inversion H1. subst t' s0 t0 s1. inversion H0. subst s0 t0 t' a.
      f_equal. apply (IHp' t).
      ++ apply H3.
      ++ apply H4.
      ++ simpl in H2. apply le_S_n. apply H2.
Qed.

Lemma longest_prefix_implies_prefix: forall (t t': trace) (p p': subtrace),
  prefix t p /\ prefix t p' /\ length p' <= length p /\ prefix t' p -> prefix t' p'.
Proof.
  intros t t' p p' [ H1 [H2 [H3 H4] ] ].
  generalize dependent t. generalize dependent t'.
  generalize dependent p. induction p'.
  - intros. apply prefix_nil.
  - intros. destruct t'. inversion H4.
    + subst p t0. inversion H2. inversion H3.
    + subst s0 t0 p. inversion H2. subst s0 t'1 t. inversion H1. subst s0 t0 s.
      apply prefix_cons. apply IHp' with (p:=t'0) (t:=t).
      ++ simpl. simpl in H3. apply le_S_n. apply H3.
      ++ subst t'1. apply H6.
      ++ subst t'1. apply H0.
      ++ subst t'1. apply H5.
Qed.

Lemma prefix_set_Singleton : forall (t : trace) (prefixes : set subtrace),
  prefixes <> (empty_set subtrace) /\ prefix_set (Singleton trace t) prefixes ->
  exists p : subtrace, set_In p prefixes /\
  (forall t' : trace, prefix t' p -> prefix_set (Singleton trace t') prefixes).
Proof.
intros t prefixes [H1 H2].
unfold prefix_set in H2. apply non_empty_gives_element in H1.
- exists (max_prefix prefixes). split.
  + apply H1.
  + intros. unfold prefix_set. intros. exists t'. split.
    ++ apply In_singleton.
    ++ apply (longest_prefix_implies_prefix t t' (max_prefix prefixes) p). repeat split.
       +++ destruct (H2 (max_prefix prefixes)).
           ++++ apply H1.
           ++++ inversion H3. inversion H4. subst x. apply H5.
       +++ destruct (H2 p).
           ++++ apply H0.
           ++++ inversion H3. inversion H4. subst x. apply H5.
       +++ apply max_prefix_longest_element. apply p. apply H0.
       +++ apply H.
- destruct prefixes.
  + unfold empty_set in H1. contradiction.
  + apply s.
Qed.

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


Definition liveness_property (p:property):=
forall (t:subtrace), exists (t':trace), prefix t' t /\ In (trace)  p t'.

Definition liveness_hyperproperty (hp: hyperproperty) :=
forall (m : Obs), exists (s:system), prefix_set s m /\ In (system)  hp s.

Lemma liveness_set_exists: forall (M:Obs), forall p : property, (forall t : subtrace,
    exists t' : trace, prefix t' t /\ In trace p t') -> exists (T: system), (forall (m:subtrace),
 (set_In m M) -> exists (x:trace), In (trace) T x  /\ prefix x m ) /\  (forall (x:trace), In (trace) T x ->In (trace) p x ).
Proof. intros M p H.  induction M.
- specialize (H []). exists p. split.
++ intros m. intros H1. inversion H1.
++ tauto.
- exists p. split.
+ intros m. intros H1. specialize (H m). destruct H. exists x. destruct H. split.
++ apply H0.
++ apply H.
+ tauto. 
Qed.


Theorem lifting_preserves_liveness:
  forall (p : property), liveness_property p <-> liveness_hyperproperty [[p]].
Proof. split; intros H.
- unfold liveness_property in H. unfold liveness_hyperproperty. intros m. pose proof liveness_set_exists. specialize (H0 m). specialize (H0 p). 
destruct H0.
++  apply H.
++ exists x. destruct H0. split.
+++ unfold prefix_set. apply H0. 
+++ apply  lifting_preserves_satisfiability. unfold satisfies_property. unfold Included. apply H1.
- unfold liveness_property. intros t. unfold liveness_hyperproperty in H. specialize (H [t]). destruct H. destruct H.
unfold prefix_set in H. specialize (H t). destruct H. 
+ unfold set_In. unfold List.In. tauto.
+  exists x0. destruct H. split.
++ apply H1.
++ apply lifting_preserves_satisfiability in H0. unfold satisfies_property in H0. unfold Included in H0. 
specialize (H0 x0). apply H0 in H. apply H.
Qed. 

Definition subset_closed_hyperproperty (hp:hyperproperty) :=
 forall (s:system) (s': system),
In (system) hp s ->  Included (trace) s' s -> In (system) hp s'.

Theorem all_lifts_are_subset_close:
forall (p:property), subset_closed_hyperproperty [[p]].
Proof. intros p. unfold subset_closed_hyperproperty. intros. apply  lifting_preserves_satisfiability.
apply  lifting_preserves_satisfiability in H. unfold satisfies_property. unfold Included.
unfold Included in H0. unfold satisfies_property in H. unfold Included in H. intros x. intros H1. specialize (H0 x). 
apply H0 in H1. specialize (H x). apply H in H1. apply H1.
Qed.

Lemma inclusion_preserves_prefix: forall (s:system) (s':system) (m: Obs),
Included (trace) s s' /\ prefix_set s m -> prefix_set s' m.
intros. destruct H. unfold Included in H. unfold prefix_set. intros p.
unfold prefix_set in H0. specialize (H0 p). intros H1. apply H0 in H1.
destruct H1. exists x. split.
- destruct H1. apply H in H1. apply H1.
- destruct H1. apply H2.
Qed.

(* This proves inclusion but not strict inclusion *)
Theorem all_safety_hyperproperties_are_subset_closed:
forall (hp: hyperproperty), safety_hyperproperty hp -> subset_closed_hyperproperty hp.
intros. unfold safety_hyperproperty in H. unfold subset_closed_hyperproperty. apply NNPP. intros H1. 
apply not_all_ex_not in H1. destruct H1. apply not_all_ex_not in H0. destruct H0. destruct H0.
intros. apply NNPP. intros H2. specialize (H x0). apply H in H2. destruct H2. specialize (H2 x). destruct H2.
pose proof conj H1 H2. apply inclusion_preserves_prefix in H4. apply H3 in H4. contradiction.
Qed.



End Hyperproperty.
