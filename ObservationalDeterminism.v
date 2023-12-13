From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Sets.Ensembles.
From Coq Require Import Lists.Streams.
From Coq Require Import Logic.Classical_Prop.
From Coq Require Import Logic.Classical_Pred_Type.
From Hyperproperties Require Import Hyperproperties.

Record ODState: Type := mkODState
  { public: nat
  ; private: nat
  }.

Module ODStateMod <: StateTypeMod.
  Definition StateType := ODState.

  Definition eq_pub (x y: ODState): bool :=
    match x, y with
    | {|public := n; private := _|},
      {|public := n'; private := _|} => Nat.eqb n n'
    end.

  Definition eq_dec: forall x y: ODState, {x = y} + {x <> y}.
  Proof.
    intros; destruct x; destruct y;
    destruct (Nat.eqb public0 public1) eqn:Heqbpub;
    destruct (Nat.eqb private0 private1) eqn:Heqbpriv.
    - apply PeanoNat.Nat.eqb_eq in Heqbpub.
      apply PeanoNat.Nat.eqb_eq in Heqbpriv.
      subst public0 private0. left. reflexivity.
    - apply PeanoNat.Nat.eqb_eq in Heqbpub. subst public0.
      apply PeanoNat.Nat.eqb_neq in Heqbpriv. right.
      unfold not in *. intros. inversion H. apply Heqbpriv. apply H1.
    - apply PeanoNat.Nat.eqb_neq in Heqbpub.
      apply PeanoNat.Nat.eqb_eq in Heqbpriv. subst private0.
      right. unfold not in *. intros. inversion H. apply Heqbpub.
      apply H1.
    - right. unfold not. intros. inversion H.
      apply PeanoNat.Nat.eqb_neq in Heqbpub. unfold not in Heqbpub.
      apply Heqbpub. apply H1.
  Qed.

  Definition eqb (x y: ODState): bool :=
    match x, y with
    | {|public := n_pub; private := n_priv|},
      {|public := n_pub'; private := n_priv'|} =>
      Nat.eqb n_pub n_pub' && Nat.eqb n_priv n_priv'
    end.

  Definition eqb_eq: forall x y: ODState, eqb x y = true <-> x = y.
  Proof.
    intros. destruct x; destruct y; split; intros.
    - inversion H. apply andb_prop in H1. destruct H1.
      apply PeanoNat.Nat.eqb_eq in H0.
      apply PeanoNat.Nat.eqb_eq in H1.
      subst public0 private0. reflexivity.
    - inversion H. subst public0 private0. simpl.
      repeat rewrite PeanoNat.Nat.eqb_refl. simpl. reflexivity.
  Qed.
End ODStateMod.

Module ODMod := Hyperproperty ODStateMod.
Import ODMod.
Import ODStateMod.

(* TODO: Can we define this constructively?
CoInductive ObservationalDeterminism: system -> Prop :=
*)

CoInductive EqSt_pub (t t': trace) : Prop :=
  eqst_pub:
  (hd t).(public) = (hd t').(public) -> EqSt_pub (tl t) (tl t') -> EqSt_pub t t'.

Lemma EqSt_pub_eq_at_all_index:
  forall (i: nat) (t t': trace),
  EqSt_pub t t' -> (Str_nth i t).(public) = (Str_nth i t').(public).
Proof.
  simple induction i.
  - intros. destruct t. destruct t'.
    inversion H. simpl in H0. unfold Str_nth.
    simpl. apply H0.
  - intros. unfold Str_nth. simpl. destruct t. destruct t'.
    simpl. apply H. apply H0.
Qed.

Lemma eq_at_all_index_EqSt_pub:
  forall (t t': trace),
  (forall (i: nat), (Str_nth i t).(public) = (Str_nth i t').(public)) -> EqSt_pub t t'.
Proof.
  cofix EqSt_pub; intros; constructor; [ clear EqSt_pub | try (apply EqSt_pub; clear EqSt_pub)].
  - apply (H 0).
  - intros. apply (H (S i)).
Qed.

Definition ObservationalDeterminism (s: system): Prop :=
  forall (t t': trace),
  In trace s t /\ In trace s t'
  /\ (hd t).(public) = (hd t').(public) -> EqSt_pub t t'.

Lemma neq_Empty_set_gives_element:
  forall {A: Type} (s: Ensemble A),
  s <> Empty_set A -> exists a: A, In A s a.
  Proof. Admitted.

Lemma not_EqSt_pub_gives_index:
  forall (t t': trace), ~ EqSt_pub t t' -> exists (i: nat),
  (Str_nth i t).(public) <> (Str_nth i t').(public).
  Proof.
    intros. unfold not in H.
    pose proof eq_at_all_index_EqSt_pub.
    specialize (H0 t t').
    apply imply_to_or in H0. destruct H0 as [H0 | H'].
    + apply not_all_ex_not in H0. apply H0.
    + apply H in H'. contradiction.
Qed.

Fixpoint build_prefix (i: nat) (t: trace): subtrace :=
  match i with
  | O => []
  | S i' => (hd t) :: build_prefix i' (tl t)
  end.

Lemma build_prefix_consistent:
  forall (i: nat) (t: trace),
  prefix t (build_prefix i t).
Proof.
  induction i.
  - intros. simpl. apply prefix_nil.
  - intros. simpl. destruct t. apply prefix_cons. simpl. apply IHi.
Qed.

Lemma build_prefix_length:
  forall (i: nat) (t: trace),
  length (build_prefix i t) = i.
Proof. induction i. intros. simpl. reflexivity.
intros. simpl. f_equal. apply IHi. Qed.

(* TODO: I think there's an off-by-one error here. *)
Lemma prefix_implies_equals:
  forall (i: nat) (t t': trace) (p: subtrace),
  prefix t p /\ prefix t' p /\ i <= length p -> Str_nth i t = Str_nth i t'.
Proof. Admitted.

Theorem ObservationalDeterminism_is_hypersafety:
  safety_hyperproperty ObservationalDeterminism.
Proof.
  unfold safety_hyperproperty. unfold In in *.
  unfold not in *.
  unfold ObservationalDeterminism in *.
  intros.
  apply not_all_ex_not in H. destruct H as [t H].
  apply not_all_ex_not in H. destruct H as [t' H].
  apply imply_to_and in H. destruct H. destruct H as [H [H' H''] ].
  apply not_EqSt_pub_gives_index in H0. destruct H0 as [i H0].
  exists [build_prefix i t; build_prefix i t'].
  intros. split.
  - unfold prefix_set. intros. inversion H1.
    + exists t. split. apply H. subst p. apply build_prefix_consistent.
    + inversion H2.
      ++ exists t'. split. apply H'. subst p. apply build_prefix_consistent.
      ++ inversion H3.
  - intros. unfold prefix_set in H1.
    assert (Hexistst1: exists t1: trace,
            In trace s' t1 /\ prefix t1 (build_prefix i t)).
    { destruct (H1 (build_prefix i t)) as [t1]. simpl. left. reflexivity.
      destruct H3. exists t1. split; assumption. }
    assert (Hexistst1': exists t1': trace,
            In trace s' t1' /\ prefix t1' (build_prefix i t')).
    { destruct (H1 (build_prefix i t')) as [t1']. simpl. right. left.
      reflexivity. destruct H3. exists t1'. split; assumption. }
    destruct Hexistst1 as [t1 [Hexistst1 Hexistst11] ].
    destruct Hexistst1' as [t1' [Hexistst1' Hexistst11'] ].
    destruct (H2 t1 t1') as [H2'].
    + repeat split.
      ++ apply Hexistst1.
      ++ apply Hexistst1'.
      ++ destruct i.
         +++ unfold not in H0. unfold Str_nth in H0. simpl in H0.
             apply H0 in H''. contradiction.
         +++ inversion Hexistst11. inversion Hexistst11'.
             subst s0 t'0 s1 t'1. simpl. apply H''.
    + apply eqst_pub in e; try apply H2'. apply EqSt_pub_eq_at_all_index with (i := i) in e.
      pose proof prefix_implies_equals.
      assert (Hteqt1: Str_nth i t = Str_nth i t1).
      { apply prefix_implies_equals with (p:= (build_prefix i t)).
        repeat split. apply build_prefix_consistent. assumption.
        rewrite build_prefix_length. apply le_n. }
      assert (Ht'eqt1': Str_nth i t' = Str_nth i t1').
      { apply prefix_implies_equals with (p:= (build_prefix i t')).
        repeat split. apply build_prefix_consistent. assumption.
        rewrite build_prefix_length. apply le_n. }
      rewrite Hteqt1 in H0.  rewrite Ht'eqt1' in H0. contradiction.
Qed.
