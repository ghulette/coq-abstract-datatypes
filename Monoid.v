Require Import Coq.Lists.List.
Import ListNotations.
Require Import Arith.

Module Type Monoid.

  Parameter t : Type.
  Parameter mempty : t.
  Parameter mappend : t -> t -> t.

  Axiom mempty_left_identity :
    forall m, mappend mempty m = m.

  Axiom mempty_right_identity :
    forall m, mappend m mempty = m.

  Axiom mappend_assoc :
    forall m n o, mappend m (mappend n o) = mappend (mappend m n) o.

End Monoid.


Module NatAddMonoid <: Monoid.
  Definition t := nat.
  Definition mempty := 0.
  Definition mappend := plus.

  Theorem mempty_left_identity :
    forall m, mappend mempty m = m.
  Proof.
    apply Nat.add_0_l.
  Qed.

  Theorem mempty_right_identity :
    forall m, mappend m mempty = m.
  Proof.
    apply Nat.add_0_r.
  Qed.

  Theorem mappend_assoc :
    forall m n o, mappend m (mappend n o) = mappend (mappend m n) o.
  Proof.
    apply Nat.add_assoc.
  Qed.

End NatAddMonoid.


Module NatMultMonoid <: Monoid.
  Definition t := nat.
  Definition mempty := 1.
  Definition mappend := mult.

  Theorem mempty_left_identity :
    forall m, mappend mempty m = m.
  Proof.
    apply Nat.mul_1_l.
  Qed.

  Theorem mempty_right_identity :
    forall m, mappend m mempty = m.
  Proof.
    apply Nat.mul_1_r.
  Qed.

  Theorem mappend_assoc :
    forall m n o, mappend m (mappend n o) = mappend (mappend m n) o.
  Proof.
    apply Nat.mul_assoc.
  Qed.

End NatMultMonoid.


Module Type Value.
  Parameter t : Type.
End Value.

Module ListMonoid (V : Value) <: Monoid.

  Definition t := list V.t.
  Definition mempty : t := [].
  Definition mappend : t -> t -> t := @app V.t.

  Theorem mempty_left_identity :
    forall m, mappend mempty m = m.
  Proof.
    apply app_nil_l.
  Qed.

  Theorem mempty_right_identity :
    forall m, mappend m mempty = m.
  Proof.
    apply app_nil_r.
  Qed.

  Theorem mappend_assoc :
    forall m n o, mappend m (mappend n o) = mappend (mappend m n) o.
  Proof.
    apply app_assoc.
  Qed.

End ListMonoid.


Module Reduce (M : Monoid).

  Fixpoint reduce (ms : list M.t) : M.t :=
    match ms with
    | [] => M.mempty
    | m::ms' => M.mappend m (reduce ms')
    end.

    Theorem reduce_one :
      forall m, reduce [m] = m.
    Proof.
      intros m.
      simpl.
      apply M.mempty_right_identity.
    Qed.

    Theorem reduce_app :
      forall l1 l2,
        reduce (l1 ++ l2) = M.mappend (reduce l1) (reduce l2).
    Proof.
      intros l1 l2.
      induction l1; simpl.
      - symmetry.
        apply M.mempty_left_identity.
      - rewrite IHl1.
        apply M.mappend_assoc.
    Qed.

End Reduce.


Module NatAddReduce := Reduce(NatAddMonoid).
Definition sum := NatAddReduce.reduce.
Compute (sum [1;2;3;4;5]).

Module NatMultReduce := Reduce(NatMultMonoid).
Definition product := NatMultReduce.reduce.
Compute (product [1;2;3;4;5]).
