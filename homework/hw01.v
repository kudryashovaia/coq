From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.



(*** Exercise 1 *)

(** 1a. Define [orb_my] function implementing boolean disjunction *)

Definition orb_my(x y : bool): bool :=
  match x with
  | true => true
  | false => y
  end.

Variable x: bool.

Compute orb_my x true.
Compute orb_my true x.
Compute orb_my x false.
Compute orb_my false x.

(** 1b. Figure out the implementation of [orb] function in the standard library
        using Coq's interactive query mechanism *)

Print orb.

Compute orb x true.
Compute orb true x.
Compute orb x false.
Compute orb false x.
(*orb is similar to orb_my*)


(** 1c. What's the difference between the standard implementation and
        the following one? *)

Definition orb_table (b c : bool) : bool :=
  match b, c with
  | true,  true  => true
  | true,  false => true
  | false, true  => true
  | false, false => false
  end.

Compute orb_table x true.
Compute orb_table true x.
Compute orb_table x false.
Compute orb_table false x.

(*Answer: Difference is that we always need x value in the last realisation to calculate the result of function*)
Print orb_table.
(** Note: the above translates into nested pattern-matching, check this *)


(** 1d. Define [addb_my] function implementing exclusive boolean disjunction.
        {The name [addb] comes from the fact this operation behaves like addition modulo 2}
        If you are already familiar with proofs in Coq, think of a prover friendly
        definition, if you are not -- experiment with how different implementations
        behave under symbolic execution. *)

Definition negb(x : bool): bool :=
  match x with
  | true => false
  | false => true
  end.


Definition addb_my(x y : bool): bool := 
  match x with
  | false => y
  | true => negb y
  end.
  
Compute addb_my x true.
Compute addb_my true x.
Compute addb_my x false.
Compute addb_my false x.


(*** Exercise 2 *)

(** 2a. Implement power function of two arguments [x] and [n],
        raising [x] to the power of [n] *)

Definition inc(n : nat): nat := S n.

Compute inc (S (S O)).

Compute muln (S (S O)) (S (S (S O))).

Fixpoint power (x y : nat) :=
  match y with
  | S y' => muln x (power x y')
  | O => (S 0)
  end. 

Compute power 2 3.

Compute predn (S(S O)).

Fixpoint sub n m :=
  match n, m with
  | S k, S l => k - l
  | _, _ => n
  end.


(*** Exercise 3 *)

(** 3a. Implement division on unary natural numbers *)

Fixpoint divmod x y q u :=
  match x with
    | 0 => (q,u)
    | S x' => match u with
                | 0 => divmod x' y (S q) y
                | S u' => divmod x' y q u'
              end
  end.

Definition divn_my x y :=
  match y with
    | 0 => y
    | S y' => fst (divmod x y' 0 y')
  end.


(* Unit tests: *)
Compute divn_my 0 0.  (* = 0 *)
Compute divn_my 1 0.  (* = 0 *)
Compute divn_my 0 3.  (* = 0 *)
Compute divn_my 1 3.  (* = 0 *)
Compute divn_my 2 3.  (* = 0 *)
Compute divn_my 3 3.  (* = 1 *)
Compute divn_my 8 3.  (* = 2 *)
Compute divn_my 42 1. (* = 42 *)
Compute divn_my 42 2. (* = 21 *)
Compute divn_my 42 3. (* = 14 *)
Compute divn_my 42 4. (* = 10 *)


(** 3b. Provide several unit tests using [Compute] vernacular command *)


(*** Exercise 4 *)

(** Use the [applyn] function defined during the lecture
    (or better its Mathcomp sibling called [iter]) define

    4a. addition on natural numbers

    4b. multiplication on natural numbers

    Important: don't use recursion, i.e. no [Fixpoint] / [fix] should be in your solution.
*)

(** Here is out definition of [applyn]: *)
Definition applyn (f : nat -> nat) :=
  fix rec (n : nat) (x : nat) :=
    if n is n'.+1 then rec n' (f x)
    else x.





