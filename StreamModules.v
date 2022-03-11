From Coq Require Import List.
Import ListNotations.

Module Type Stream.
Parameter t : Type -> Type.
Parameter cons : forall A, A -> t A -> t A.
Parameter head : forall A, t A -> A.
Parameter tail : forall A, t A -> t A.
Parameter take : forall A, nat -> t A -> list A.
Parameter map : forall A, (A -> A) -> t A -> t A.
(* Parameter fold_map : forall A B C, (A -> B -> A*C) -> A -> t B -> t C.
Parameter build : forall A B, (A -> A*B) -> A -> t B.
Parameter repeat : forall A, A -> t A. *)
Parameter zip_with : forall A B C, (A -> B -> C) -> t A -> t B -> t C.
End Stream.

(* CoInductively defined streams *)
Module CoIndStream <: Stream.

CoInductive stream (A : Type) : Type :=
| Cons : A -> stream A -> stream A.

Definition t := stream.

Definition cons {A : Type} (x : A) (s : t A) : t A :=
  Cons _ x s.

Definition head {A : Type} (s : t A) : A :=
  match s with
  | Cons _ x _ => x
  end.

Definition tail {A : Type} (s : t A) : t A :=
  match s with
  | Cons _ _ s' => s'
  end.

Fixpoint take {A : Type} (n : nat) (s : t A) : list A :=
  match n with
  | 0 => []
  | S n' =>
    match s with
    | Cons _ x s' => x :: take n' s'
    end
  end.

CoFixpoint map {A : Type} (f : A -> A) (s : t A) : t A :=
  match s with
  | Cons _ x s' => cons (f x) (map f s')
  end.

CoFixpoint fold_map {A B C: Type} (f : A -> B -> A*C) (a : A) (bs : t B) : t C :=
  match bs with
  | Cons _ b bs' =>
    let '(a',c) := f a b in
    cons c (fold_map f a' bs')
  end.

CoFixpoint build {A B : Type} (f : A -> A*B) (a : A) : t B :=
  let '(a', b) := f a in
  cons b (build f a').

Definition repeat {A : Type} (x : A) : t A :=
  build (fun x => (x,x)) x.

CoFixpoint zip_with {A B C : Type} (f : A -> B -> C) (sa : t A) (sb : t B) : t C :=
  match sa, sb with
  | Cons _ a sa', Cons _ b sb' => cons (f a b) (zip_with f sa' sb')
  end.

End CoIndStream.

(* Streams defined by functions from nat *)
Module NatFStream : Stream.

Definition t (A : Type) := nat -> A.

Definition cons {A : Type} (x : A) (s : t A) : t A :=
  fun n => match n with
  | O => x
  | S n' => s n'
  end.

Definition head {A : Type} (s : t A) : A := s O.

Definition tail {A : Type} (s : t A) : t A :=
  fun n => s (S n).

Definition take {A : Type} (n : nat) (s : t A) : list A :=
  let fix aux i :=
    match i with
    | O => []
    | S i' => s i' :: aux i'
    end
  in
  List.rev (aux n).

Definition map {A : Type} (f : A -> A) (s : t A) : t A :=
  fun n => f (s n).

Definition zip_with {A B C : Type} (f : A -> B -> C) (sa : t A) (sb : t B) : t C :=
  fun n => f (sa n) (sb n).

End NatFStream.


Section Fibs.
  Import CoIndStream.
  Fail CoFixpoint fibs_zip : t nat :=
    cons 0 (cons 1 (zip_with (fun x y => x + y) fibs_zip (tail fibs_zip))).
End Fibs.

Section FibsNat.
  Import NatFStream.
  Fail Fixpoint fibs_zip : t nat :=
    cons _ 0 (cons _ 1 (zip_with (fun x y => x + y) fibs_zip (tail fibs_zip))).
End FibsNat.
