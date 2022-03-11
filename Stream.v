From Coq Require Import List.
Import ListNotations.
From Coq Require Import FunctionalExtensionality.

Module Stream.

CoInductive t (A : Type) : Type :=
| Cons : A -> t A -> t A.

Definition cons {A : Type} (x : A) (s : t A) : t A :=
  Cons _ x s.

CoInductive bisim {A : Type} : t A -> t A -> Prop :=
| Stream_bisim : forall x s1 s2, bisim s1 s2 -> bisim (Cons _ x s1) (Cons _ x s2).

Definition decomp {A : Type} (s : t A) : t A :=
  match s with
  | Cons _ x s => cons x s
  end.

Lemma decomp_eq :
  forall A (s : t A), s = decomp s.
Proof.
  destruct s; reflexivity.
Qed.

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

CoFixpoint from_natf_n {A : Type} (f : nat -> A) (n : nat) : t A :=
  cons (f n) (from_natf_n f (S n)).

Definition from_natf {A : Type} (f : nat -> A) : Stream.t A :=
  from_natf_n f 0.

Fixpoint to_natf {A : Type} (s : t A) (n : nat) : A :=
  match n with
  | 0 => head s
  | S n' => to_natf (tail s) n'
  end.

Theorem to_from_natf_iso :
  forall (A : Type) (s : t A),
    bisim (from_natf (to_natf s)) s.
Proof.
  intro A.
  cofix HC.
  intro s.
  rewrite (decomp_eq _ (from_natf (to_natf s))); simpl.
  destruct s.
  apply Stream_bisim.
Abort.

Theorem from_to_natf_iso :
  forall (A : Type) (f : nat -> A),
    bisim_eq ->
    to_natf (from_natf f) = f.
Proof.
  intros.
  apply functional_extensionality.
  intro n.
  generalize dependent f.
  induction n; intros f.
  - reflexivity.
  - specialize IHn with (fun i => f (S i)).
    rewrite <- IHn.
    simpl.
    f_equal.
    unfold from_natf.
    apply H.
    cofix C.
    rewrite (decomp_eq _ (from_natf_n f 1)).
    rewrite (decomp_eq _ (from_natf_n (fun i : nat => f (S i)) 0)).
    simpl.
    constructor.
Abort.

End Stream.

Compute Stream.take 5 (Stream.from_natf (fun x => x + 1)).

Definition from_natf {A : Type} (f : nat -> A) : Stream.t A :=
  Stream.build (fun i => (i+1, f i)) 0.

Definition fibs : Stream.t nat :=
  Stream.build (fun '(x, y) => ((y, y+x), x)) (1, 1).

Compute Stream.take 15 Stream.fibs.
Compute Stream.take 10 (Stream.map (fun x => x * 2) (Stream.build (fun x => (x + 1, x)) 0)).
