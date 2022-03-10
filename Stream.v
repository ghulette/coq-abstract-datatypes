From Coq Require Import List.
Import ListNotations.

Module Stream.

CoInductive t (A : Type) : Type :=
| Cons : A -> t A -> t A.

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

Fail CoFixpoint fibs_zip :=
  cons 0 (cons 1 (zip_with (fun x y => x + y) fibs_zip (tail fibs_zip))).

End Stream.

Definition fibs : Stream.t nat :=
  Stream.build (fun '(x, y) => ((y, y+x), x)) (1, 1).

Compute Stream.take 15 Stream.fibs.
Compute Stream.take 10 (Stream.map (fun x => x * 2) (Stream.build (fun x => (x + 1, x)) 0)).
