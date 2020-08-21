Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* A monoid is a type equipped with an append operation and an empty element
that "does nothing" with respect to the append operation. It turns out that
monoids are a very useful and general abstract data type.

In Coq, we can add "proof obligations" to this datatype, that show that an
instance of monoid behaves the right way. In particular, we want the empty to
behave like unit, and append must be associative. *)
Record Monoid := {
  (* The abstract monoid type. *)
  t : Type;

  (* Empty element is an instance of t. *)
  empty : t;

  (* The append operation. *)
  append : t -> t -> t;

  (* The proof obligations or specification. *)
  left_identity : forall m, append empty m = m;
  right_identity : forall m, append m empty = m;
  assoc : forall m n o, append m (append n o) = append (append m n) o;
}.

(* Natural numbers form a monoid under addition, with 0 as empty element. *)
Definition NatAddMonoid : Monoid := {|
  t := nat;
  empty := 0;
  append := plus;
  left_identity := Nat.add_0_l;
  right_identity := Nat.add_0_r;
  assoc := Nat.add_assoc;
|}.

(* Natural numbers also form a monoid under multiplication, with 1 as the
empty element. *)
Definition NatMultMonoid : Monoid := {|
  t := nat;
  empty := 1;
  append := mult;
  left_identity := Nat.mul_1_l;
  right_identity := Nat.mul_1_r;
  assoc := Nat.mul_assoc;
|}.

(* Next we define a (very simple) algorithm on monoids. The key idea is that
reduce will work for *any* monoid, without knowing anything beyond the
abstract Monoid specification.

Furthermore, we can *prove* reduce will behave as per a specification without
knowing anything about any particular monoid.

It's like saying, "give me a monoid, and I will give you a reduce operation on
that monoid. And if you can prove your monoid really does behave like a
monoid, then I will prove that reduce will behave like reduce ought to."
*)
Section Reduce.
  Variable m : Monoid.

  Fixpoint reduce (xs : list m.(t)) : m.(t) :=
    match xs with
    | [] => m.(empty)
    | x::xs' => m.(append) x (reduce xs')
    end.

  Theorem reduce_one :
    forall x, reduce [x] = x.
  Proof.
    intros x.
    simpl.
    apply m.(right_identity).
  Qed.

  Theorem reduce_app :
    forall l1 l2,
      reduce (l1 ++ l2) = m.(append) (reduce l1) (reduce l2).
  Proof.
    intros l1 l2.
    induction l1; simpl.
    - symmetry.
      apply m.(left_identity).
    - rewrite IHl1.
      apply m.(assoc).
  Qed.
End Reduce.

(* Using the abstract idea of reduce, along with our concrete monoid instance
of natural numbers under addition, it is very easy to define summation... *)
Definition sum : list nat -> nat := reduce NatAddMonoid.
Compute (sum [1;2;3;4;5]).

(* ... and to prove useful, concrete things about how it behaves. *)
Theorem sum_app :
  forall ns ms, sum (ns ++ ms) = sum ns + sum ms.
Proof.
  exact (reduce_app NatAddMonoid).
Qed.

(* Same idea but for product. *)
Definition product : list nat -> nat := reduce NatMultMonoid.
Compute (product [1;2;3;4;5]).


(* Lists form a monoid under concatenation. This definition has to be parametric
in the list element type. *)
Section ListMonoidDef.

  (* Parametric type of list elements. *)
  Variable A : Type.

  Definition ListMonoid : Monoid := {|
    t := list A;
    empty := [];
    append := @app A;
    left_identity := @app_nil_l A;
    right_identity := @app_nil_r A;
    assoc := @app_assoc A;
  |}.
End ListMonoidDef.

(* Flatten takes a list of lists and combines them all into one list. *)
Definition flatten {A : Type} : list (list A) -> list A :=
  reduce (ListMonoid A).

Compute (flatten [[1;2;3]; [4;5]]).
