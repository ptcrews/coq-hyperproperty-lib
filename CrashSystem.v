From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Lists.ListSet.
From Coq Require Import Logic.Classical_Pred_Type.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Sets.Finite_sets.
From Hyperproperties Require Import Hyperproperties.

Inductive State : Type :=
  | CrashState : State
  | RunningState : State.

Module CrashStateMod <: StateTypeMod.
  Definition StateType := State.
  Definition eq_dec: forall x y: State, {x = y} + {x <> y}.
  Proof. intros; destruct x; destruct y.
  - left. reflexivity.
  - right. intros contra. inversion contra.
  - right. intros contra. inversion contra.
  - left. reflexivity.
  Qed.
  Definition eqb (x y: State) : bool :=
    match x, y with
    | CrashState, CrashState => true
    | RunningState, RunningState => true
    | _, _ => false
    end.
  Definition eqb_eq: forall x y: State, eqb x y = true <-> x = y.
    Proof. intros; destruct x; destruct y; split; intros; try inversion H; reflexivity.
    Qed.
End CrashStateMod.

Module CrashHyperMod := Hyperproperty CrashStateMod.
Import CrashHyperMod.
Import CrashStateMod.

CoFixpoint crash_trace : psi_inf := Cons CrashState crash_trace.
Example crash_system : system := Singleton trace crash_trace.

(* An example property which describes the crash program. *)
Example crash_property : property := Singleton trace crash_trace.
Check crash_property.
Example crash_hyperproperty : hyperproperty :=
  Add system (Singleton system crash_system) (Singleton trace crash_trace).

Lemma crash_property_in_PROP : In property PROP crash_property.
Proof. constructor. Qed.

Lemma crash_hyperproperty_in_HP : In hyperproperty HP crash_hyperproperty.
Proof. constructor. Qed.

Lemma crash_system_satisfies_crash_property :
  satisfies_property crash_system crash_property.
Proof. intros x H. inversion H. constructor. Qed.

Lemma crash_system_satisfies_crash_hyperproperty :
  satisfies_hyperproperty crash_system crash_hyperproperty.
Proof. constructor. apply In_singleton. Qed.

Lemma crash_property_lifts_to_crash_hyperproperty :
  forall s: system, satisfies_property s crash_property <-> 
  satisfies_hyperproperty s [[crash_property]].
Proof. intros s. apply lifting_preserves_satisfiability. Qed.

Lemma crash_state_prefix_crash_trace :
  prefix crash_trace [CrashState].
Proof.
  rewrite (unfold_Stream crash_trace). repeat constructor.
Qed.

Definition eqb_eq_if: forall x y: State, eqb x y = true -> x = y.
Proof. intros. apply eqb_eq. apply H. Qed.

Definition eqb_eq_oif: forall x y: State, x = y -> eqb x y = true.
Proof. intros. apply eqb_eq. apply H. Qed.

Inductive NeqSt {A: Type} (s s': Stream A) : Prop :=
  | Neqst_head: hd s <> hd s' -> NeqSt s s'
  | Neqst_tail: NeqSt (tl s) (tl s') -> NeqSt s s'.

Lemma neqst_stream_gives_nth: forall {A: Type} (s s': Stream A),
  NeqSt s s' <-> exists (n: nat), Str_nth n s <> Str_nth n s'.
Proof.
  split; intros.
  - induction H. 
    + exists 0. unfold Str_nth. simpl. apply H.
    + destruct IHNeqSt. exists (S x). unfold Str_nth in *. simpl in *. apply H0.
  - destruct H. generalize dependent s. generalize dependent s'.
    induction x.
    + intros. apply Neqst_head. unfold Str_nth in H. simpl in H. apply H.
    + intros. apply Neqst_tail. apply IHx. apply H.
Qed.

Lemma neqst_iff_not_equals: forall {A: Type} (s s': Stream A),
  NeqSt s s' <-> ~ EqSt s s'.
Proof.
  split; intros.
  - unfold not. intros. rewrite neqst_stream_gives_nth in H. destruct H.
    apply (eqst_ntheq x) in H0. unfold not in H. apply H in H0.
    contradiction.
  - apply neqst_stream_gives_nth. apply not_all_not_ex. unfold not.
    intros. unfold not in H. apply H. apply ntheq_eqst. intros n.
    specialize (H0 n). apply NNPP in H0. apply H0.
Qed.

Fixpoint get_prefix (n: nat) (t: trace) : subtrace :=
  match n with
  | O => [hd t]
  | S m => [hd t] ++ get_prefix m (tl t)
  end.

Lemma get_prefix_is_prefix: forall (n: nat) (t: trace),
  prefix t (get_prefix n t).
Proof.
  intros n. induction n.
  - intros. simpl. destruct t. apply prefix_cons. apply prefix_nil.
  - intros. simpl. destruct t. apply prefix_cons. simpl. apply IHn.
Qed.


(* TODO(ptcrews): This is equivalent to assuming functional extensionality. We
 * can likely omit it, but would have to rework Ensemble to use EqSt/NeqSt
 * instead of propositional equality "=" *)
Lemma NeqSt_eq_neq: forall (t t': trace),
  NeqSt t t' <-> t <> t'.
Proof. Admitted.

Lemma neqst_trace_gives_prefix: forall (t t': trace),
  NeqSt t t' <-> exists (p: subtrace), ~prefix t p /\ prefix t' p.
Proof.
  split.
  - intros. induction H.
    + exists ([hd s']).
      split.
      ++ unfold not. intros. inversion H0.
         subst s. simpl in H. contradiction.
      ++ destruct s'. apply prefix_cons. apply prefix_nil.
    + destruct s. destruct s'.
      destruct IHNeqSt as [p [IHNeqSt IHNeqSt'] ].
      exists (s1 :: p).
      split.
      ++ simpl in *. unfold not. intros contra.
         unfold not in IHNeqSt.
         apply IHNeqSt.
         inversion contra.
         subst s2 s0 s1 t'. apply H1.
      ++ apply prefix_cons. simpl in *. apply IHNeqSt'.
  - intros. destruct H as [p [H H'] ].
    apply NeqSt_eq_neq. unfold not. intros. subst t'.
   apply H in H'. contradiction.
Qed.

Lemma neq_singleton_iff_neq_element: forall (t t': trace),
  ~ In trace (Singleton trace t) t' <-> t <> t'.
Proof. intros t t'. split.
+ intros H. unfold not. intros H1. apply H. rewrite H1 in *. apply In_singleton.
+ intros H. intros H1. apply H. destruct H1. contradiction. 
Qed.

Theorem crash_property_is_SP: safety_property crash_property.
Proof. unfold safety_property. intros.
apply neq_singleton_iff_neq_element in H.
apply NeqSt_eq_neq in H. apply neqst_trace_gives_prefix in H.
destruct H as [p [H' H''] ] eqn:H1. exists p.
intros. split.
+ apply H''.
+ intros. apply neq_singleton_iff_neq_element. apply NeqSt_eq_neq.
  apply neqst_trace_gives_prefix. exists p. split.
  ++ apply H'.
  ++ apply H0.
Qed.

Theorem crash_hyperproperty_is_SHP: safety_hyperproperty [[crash_property]].
Proof.
  apply lifting_preserves_safety. apply crash_property_is_SP. Qed.
