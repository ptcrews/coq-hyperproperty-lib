From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Lists.Streams.
From Coq Require Import Sets.Ensembles.
From Hyperproperties Require Import Hyperproperties.

Inductive GSState :=
  | Request (tag: nat) : GSState
  | Response (tag: nat) : GSState
  | Bottom: GSState.

Module GSStateMod <: StateTypeMod.
  Definition StateType := GSState.
  Definition eq_dec: forall x y: GSState, {x = y} + {x <> y}.
  Proof.
    intros; destruct x; destruct y.
    - destruct (Nat.eqb tag tag0) eqn:Htag.
      + apply PeanoNat.Nat.eqb_eq in Htag. subst tag. left. reflexivity.
      + apply PeanoNat.Nat.eqb_neq in Htag. right. unfold not in *. intros.
        apply Htag. inversion H. reflexivity.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - destruct (Nat.eqb tag tag0) eqn:Htag.
      + apply PeanoNat.Nat.eqb_eq in Htag. subst tag. left. reflexivity.
      + apply PeanoNat.Nat.eqb_neq in Htag. right. unfold not in *. intros.
        apply Htag. inversion H. reflexivity.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - right. unfold not. intros. inversion H.
    - left. reflexivity.
  Qed.
  Definition eqb (x y: GSState) : bool :=
    match x, y with
    | Request n, Request n' => Nat.eqb n n'
    | Response n, Response n' => Nat.eqb n n'
    | Bottom, Bottom => true
    | _, _ => false
    end.

  Definition eqb_eq: forall x y: GSState, eqb x y = true <-> x = y.
  Proof. intros. destruct x; destruct y; split; intros; try inversion H; simpl;
    try reflexivity.
    - apply PeanoNat.Nat.eqb_eq in H1. subst tag0. reflexivity.
    - apply PeanoNat.Nat.eqb_refl.
    - apply PeanoNat.Nat.eqb_eq in H1. subst tag0. reflexivity.
    - apply PeanoNat.Nat.eqb_refl.
  Qed.
End GSStateMod.

Module GSMod := Hyperproperty GSStateMod.
Import GSMod.
Import GSStateMod.

CoFixpoint bottom_trace: psi_inf := Cons Bottom bottom_trace.
Definition bottom_system: system := Singleton trace bottom_trace.

Fixpoint insert_at_index {A: Type} (n: nat) (a: A) (s: Stream A): Stream A :=
  match n with
  | O => Cons a s
  | S m => Cons (hd s) (insert_at_index m a (tl s))
  end.

CoInductive GuaranteedService: trace -> Prop :=
  | GSBottom: GuaranteedService bottom_trace
  | GSConsRequest (tag i: nat) (t: trace) (H: GuaranteedService t):
      GuaranteedService (Cons (Request tag) (insert_at_index i (Response tag) t))
  | GSConsBottom (t: trace) (H: GuaranteedService t):
      GuaranteedService (Cons Bottom t)
  | GSConsResponse (tag: nat) (t: trace) (H: GuaranteedService t):
      GuaranteedService (Cons (Response tag) t).

Lemma bottom_trace_is_Bottom: forall i: nat,
  Str_nth i bottom_trace = Bottom.
Proof.
  induction i.
  - unfold Str_nth. simpl. reflexivity.
  - unfold Str_nth. case IHi. simpl. constructor.
Qed.

(* A more intuitive definition of Guaranteed Service. *)
Definition all_requests_have_responses (t: trace): Prop :=
  forall (tag i: nat) (s: GSState),
  Str_nth i t = Request tag -> exists i': nat, i <= i' /\ Str_nth i' t = Response tag.

(* TODO: We should probably prove this, but for now we claim it is correct. *)
Theorem GuaranteedService_is_consistent:
  forall t: trace, all_requests_have_responses t <-> GuaranteedService t.
intros t. split.
+ intros H. unfold all_requests_have_responses in H. induction  tag i.
Proof. Admitted.

Lemma bottom_trace_is_GuaranteedService: In trace GuaranteedService bottom_trace.
Proof.
  unfold In. apply GSBottom.
Qed.

Lemma prefix_preserved_if_insert_after:
  forall (n: nat) (s: GSState) (t: trace) (p: subtrace),
   prefix t p /\ length p <= n -> prefix (insert_at_index n s t) p.
Proof.
  induction n.
  - intros s t p [H H']. simpl. inversion H'. apply length_zero_iff_nil in H1.
    subst p. apply prefix_nil.
  - intros s t p [H H']. simpl. inversion H.
    + subst p t0. apply prefix_nil.
    + subst p t. apply prefix_cons. apply IHn. split.
      ++ simpl. apply H0.
      ++ apply le_S_n . simpl in H'. apply H'.
Qed.

Theorem GuaranteedService_is_liveness: liveness_property GuaranteedService.
Proof.
  unfold liveness_property. intros p. induction p.
  - exists bottom_trace. split. apply prefix_nil.
    apply bottom_trace_is_GuaranteedService.
  - destruct IHp as [t [Hp Hp'] ]. unfold In in *. destruct a eqn:Ha.
    + apply (GSConsRequest tag (length p) t) in Hp'.
      exists (Cons (Request tag) (insert_at_index (length p) (Response tag) t)).
      split.
      ++ apply prefix_cons. apply prefix_preserved_if_insert_after. split.
         apply Hp. apply le_n.
      ++ apply Hp'.
    + apply (GSConsResponse tag t) in Hp'.
      exists (Cons (Response tag) t). split. constructor. apply Hp.
      apply Hp'.
    + exists (Cons Bottom t). split. constructor. apply Hp.
      apply GSConsBottom in Hp'. apply Hp'.
Qed.
