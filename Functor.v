Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Program. (* Exports functional extensionality. *)

Record Functor (F : Type -> Type) := {
  fmap : forall (A B : Type), (A -> B) -> F A -> F B;
  fmap_identity : forall (A : Type), fmap A A id = id;
  fmap_compose : forall (A B C : Type) (f : B -> C) (g : A -> B),
    compose (fmap B C f) (fmap A B g) = fmap A C (compose f g);
}.

Program Definition OptionFunctor : Functor option := {|
    fmap A B f m :=
      match m with
      | Some x => Some (f x)
      | None => None
      end;
|}.

Next Obligation.
  unfold id.
  apply functional_extensionality.
  intros x.
  destruct x; reflexivity.
Qed.

Next Obligation.
  unfold compose.
  apply functional_extensionality.
  intros x.
  destruct x; reflexivity.
Qed.
