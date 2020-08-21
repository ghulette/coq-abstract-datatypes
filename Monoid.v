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
