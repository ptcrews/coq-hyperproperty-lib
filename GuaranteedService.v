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
  Proof. Admitted.
  Definition eqb (x y: GSState) : bool :=
    match x, y with
    | Request n, Request n' => Nat.eqb n n'
    | Response n, Response n' => Nat.eqb n n'
    | _, _ => false
    end.

  Definition eqb_eq: forall x y: GSState, eqb x y = true <-> x = y.
  Proof. Admitted.
End GSStateMod.

Module GSMod := Hyperproperty GSStateMod.
Import GSMod.
Import GSStateMod.

Definition all_requests_have_responses (t: trace): Prop :=
  forall (tag i: nat) (s: GSState),
  Str_nth i t = Request tag -> exists i': nat, i <= i' /\ Str_nth i' t = Response tag.

Definition GuaranteedService : property := all_requests_have_responses.

CoFixpoint bottom_trace: psi_inf := Cons Bottom bottom_trace.
Definition bottom_system: system := Singleton trace bottom_trace.

Fixpoint prepend_to_Stream {A: Type} (l: list A) (s: Stream A): Stream A :=
  match l with
  | [] => s
  | a :: l' => Cons a (prepend_to_Stream l' s)
  end.

Lemma prepend_to_Stream_gives_prefix: forall (p: subtrace) (t: trace),
  prefix (prepend_to_Stream p t) p.
Proof.
  induction p.
  - intros. simpl. apply prefix_nil.
  - simpl. destruct t. apply prefix_cons. apply IHp.
Qed.

Lemma bottom_trace_is_Bottom: forall i: nat,
  Str_nth i bottom_trace = Bottom.
Proof.
  induction i.
  - unfold Str_nth. simpl. reflexivity.
  - unfold Str_nth. case IHi. simpl. constructor.
Qed.

Lemma bottom_trace_is_GuaranteedService: In trace GuaranteedService bottom_trace.
Proof.
  unfold In. unfold GuaranteedService. unfold all_requests_have_responses.
  intros. rewrite bottom_trace_is_Bottom in H. inversion H.
Qed.

Lemma GuaranteedService_preserved_under_insertion:
  forall (p: subtrace) (t: trace) (tag: nat),
  GuaranteedService t /\ prefix t p ->
  GuaranteedService (prepend_to_Stream (Request tag :: p ++ [Response tag]) t).
Proof.
  intros p. induction p.
  - intros. simpl. unfold GuaranteedService. unfold all_requests_have_responses.
    intros. exists (S O). unfold Str_nth in *. simpl in *.
    admit.
  - admit.
Admitted.

Theorem GuaranteedService_is_liveness: liveness_property GuaranteedService.
Proof.
  unfold liveness_property. intros p. induction p.
  - exists bottom_trace. split. apply prefix_nil.
    apply bottom_trace_is_GuaranteedService.
  - destruct IHp as [t [Hp Hp'] ]. destruct a eqn:Ha.
    (* TODO: I'm not sure this step is correct; we want to prepent Request tag,
     * but then insert Response tag *after* p, not preprend the entire thing *)
    + exists (prepend_to_Stream (Request tag :: p ++ [Response tag]) t).
      split.
      ++ simpl. apply prefix_cons. admit.
      ++ simpl. apply GuaranteedService_preserved_under_insertion.
         split; assumption.
    + exists (prepend_to_Stream (Response tag :: p) t). split.
      ++ simpl. apply prefix_cons. apply prepend_to_Stream_gives_prefix.
      ++ simpl. admit.
    + admit.
Admitted.
