Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* A monoid is a type equipped with an append operation and an empty element
that "does nothing" with respect to the append operation. It turns out that
monoids are a very useful and general abstract data type.

In Coq, we can add "proof obligations" to this datatype, that show that an
instance of monoid behaves the right way. In particular, we want the empty
value to behave like unit, and append must be associative. *)
Record Monoid (A : Type) := {

  (* Empty element is an instance of A. *)
  empty : A;

  (* The append binary operation. *)
  append : A -> A -> A;

  (* The proof obligations (i.e., a formal specification). *)
  left_identity : forall m, append empty m = m;
  right_identity : forall m, append m empty = m;
  assoc : forall m n o, append m (append n o) = append (append m n) o;
}.

(* Natural numbers form a monoid under addition, with 0 as empty element. *)
Program Definition NatAddMonoid : Monoid nat := {|
  empty  := 0;
  append := plus;
|}.

(* Coq can prove left_identity (that is, forall n, 0 + n = n) and
right_identity (forall n, n + 0 = n) automatically, but it fails on assoc so
we need to help. To satisify this obligation we have to prove that
forall m n o, m + (n + o) = (m + n) + o.*)
Next Obligation. apply Nat.add_assoc. Qed.

(* Natural numbers also form a monoid under multiplication, with 1 as the
empty element. *)
Program Definition NatMultMonoid : Monoid nat := {|
  empty  := 1;
  append := mult;
|}.
Next Obligation. apply Nat.mul_1_r. Qed.
Next Obligation. apply Nat.mul_assoc. Qed.

(* Next we define a (very simple) algorithm on monoids. The key idea is that
reduce will work for *any* monoid, without knowing anything beyond the
abstract Monoid specification.

Moreover, in Coq we can use our monoid facts (identity and assoc) to *prove*
reduce will behave as per a specification without knowing anything else about
any particular monoid.

It's like saying, "give me a monoid, and I will give you a reduce operation on
that monoid. And if you can prove your monoid really does behave like a
monoid, then I will prove that reduce will behave like reduce ought to."
*)
Section Reduce.
  Variable A : Type.
  Variable m : Monoid A.
  (* It might help to think of m as *evidence* that A implements Monoid. *)

  Fixpoint reduce (xs : list A) : A :=
    match xs with
    | [] => empty _ m
    | x::xs' => append _ m x (reduce xs')
    end.

  Theorem reduce_one :
    forall x, reduce [x] = x.
  Proof.
    intros x.
    simpl.
    apply (right_identity _ m).
  Qed.

  Theorem reduce_app :
    forall l1 l2,
      reduce (l1 ++ l2) = append _ m (reduce l1) (reduce l2).
  Proof.
    intros l1 l2.
    induction l1; simpl.
    - symmetry.
      apply (left_identity _ m).
    - rewrite IHl1.
      apply (assoc _ m).
  Qed.
End Reduce.

(* Using the abstract idea of reduce, along with our concrete monoid instance
of natural numbers under addition, it is very easy to define summation... *)
Definition sum : list nat -> nat := reduce _ NatAddMonoid.
Compute (sum [1;2;3;4;5]).

(* ... and to prove useful, concrete things about how it behaves. *)
Theorem sum_app :
  forall ns ms, sum (ns ++ ms) = sum ns + sum ms.
Proof.
  (* This is just an instance of our reduce_app proof from above. *)
  exact (reduce_app _ NatAddMonoid).
Qed.

(* Same idea but for product. *)
Definition product : list nat -> nat := reduce _ NatMultMonoid.
Compute (product [1;2;3;4;5]).

Theorem product_app :
  forall ns ms, product (ns ++ ms) = product ns * product ms.
Proof.
  exact (reduce_app _ NatMultMonoid).
Qed.


(* One more example. Lists of elements drawn from some arbitrary type form a
monoid under concatenation. This definition has to be parametric in the list
element type. We are effectively defining a *family* of monoids here -- for
every type A, the type list A is a monoid. *)
Program Definition ListMonoid (A : Type) : Monoid (list A) := {|
  empty  := [];
  append := @app A;
|}.

Next Obligation. apply app_nil_r. Qed.
Next Obligation. apply app_assoc. Qed.

(* Flatten takes a list of lists and combines them all into one list. *)
Definition flatten {A : Type} : list (list A) -> list A :=
  reduce _ (ListMonoid _).

Compute (flatten [[1;2;3]; [4;5]; []; [6;7;8;9;10]]).


(* Exercise: come up with a monoid instance for bool (as with nat, which we
saw had instances for both add and mult, for bool there's more than one
possible instance). What would be a good function name for reduce on your
instance? *)

(** FILL IN HERE
Program Definition BoolMonoid : Monoid bool := {|
  empty  := *a boolean value* ;
  append := *a binary operation on bool* ;
|}.

Next Obligation. ****

Definition **** : list bool -> bool := reduce _ BoolMonoid.
*)
