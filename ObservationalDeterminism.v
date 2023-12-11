From Coq Require Import Sets.Ensembles.
From Coq Require Import Lists.Streams.
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

Definition ObservationalDeterminism (s: system): Prop :=
  forall (t t': trace),
  In trace s t /\ In trace s t'
  /\ (hd t).(public) = (hd t').(public) -> EqSt_pub t t'.

Theorem ObservationalDeterminism_is_hypersafety:
  safety_hyperproperty ObservationalDeterminism.
Proof. Admitted.
