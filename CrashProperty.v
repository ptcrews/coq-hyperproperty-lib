From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Sets.Powerset.
From Coq Require Import Lists.ListSet.
From Coq Require Import Logic.Classical_Pred_Type.
From Coq Require Import Logic.Classical_Prop.
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

CoFixpoint halt_trace : psi_inf := Cons CrashState halt_trace.
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

Lemma crash_property_lifts_to_crash_hyperproperty :
  forall s: system, satisfies_property s crash_property <-> 
  satisfies_hyperproperty s [[crash_property]].
Proof. intros s. apply lifting_preserves_satisfiability. Qed.

Lemma crash_state_prefix_crash_trace :
  prefix halt_trace [CrashState].
Proof.
  rewrite (unfold_Stream halt_trace). repeat constructor.
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

Lemma prefix_equals_str_nth: forall (n: nat) (s: subtrace) (t: trace),
  prefix t s /\ n <= length s /\ s <> [] -> nth_error s n = Some (Str_nth n t).
Proof.
  induction n.
  - intros s t [H [H' H''] ]. simpl. destruct s. contradiction.
    destruct t. inversion H. unfold Str_nth. simpl. reflexivity.
  - intros s t [H [H' H''] ].
    destruct s; try contradiction.
    simpl. apply IHn. repeat split.
    + destruct t. inversion H. simpl. apply H1.
    + simpl in H'. apply le_S_n. apply H'.
    + admit.
Admitted.

Lemma neqst_trace_gives_prefix: forall (t t': trace),
  NeqSt t t' <-> exists (p: subtrace), ~prefix t p /\ prefix t' p.
Proof. Admitted.

Lemma neq_singleton_iff_neq_element: forall (t t': trace),
  ~ In trace (Singleton trace t) t' <-> t <> t'.
Proof. Admitted.

(* TODO(ptcrews): This is equivalent to assuming functional extensionality. We
 * can likely omit it, but would have to rework Ensemble to use EqSt/NeqSt
 * instead of propositional equality "=" *)
Lemma NeqSt_eq_neq: forall (t t': trace),
  NeqSt t t' <-> t <> t'.
Proof. Admitted.

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
