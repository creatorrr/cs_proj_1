(*** Coq in a Hurry ***)
(*+ Tutorial Exercises +*)

(** *Section 1* **)

Check True : Prop.
Check False : Prop.
Check 3 : nat.
Check (3+5) : nat.
Check (3=5) : Prop.
Check (3=5) /\ True : Prop.
Check nat -> Prop : Type.
Check (3 <= 6) : Prop.
Check (3, 3=5) : nat * Prop.

Check (fun x:nat => x=3) : nat -> Prop.
Check (forall x:nat, x < 3 \/ (exists y:nat, x = y + 3)) : Prop.
Check (let f := fun x => (x*3, x) in f 3) : nat*nat.

Locate "_ <= _".

Check (and True False) : Prop.
Check and : Prop -> Prop -> Prop.
Check Prop -> (Prop -> Prop) : Type.

Eval compute in
    let f := fun x => (x*3, x) in
    f 3.

(** Exercise on functions **)
Definition fun_add_5 := fun a b c d e => (a + b + c + d + e).
Check fun_add_5 : nat -> nat -> nat -> nat -> nat -> nat.
Eval compute in fun_add_5 1 2 3 4 5 : nat.
Eval compute in (fun_add_5 1 2 3 4 5) = 15 : Prop.


(** *Section 2* **)

Definition example1 (x : nat) := x*x + 2*x + 1.
Check example1.
(*
Reset example1.
Print example1.
*)

Require Import Bool.

Eval compute in if true then 3 else 5.
Search bool.

Require Import Arith.

Definition is_zero (x : nat) :=
  match x with
    0 => true
  | S p => false
  end.

Print pred.
(*
Definition pred (n : nat) :=
    match n with
      0 => n
    | S u => u
    end.
 *)

(** **Structural recursion** **)
(**
Coq imposes limitations on iteration/recursion to ensure that all programs only have
finite running time. This is to avoid the halting problem which would render a theorem
prover useless.

The specific limitation is called _structural recursion_ and it entails that functions
with recursive definitions should:

 - Use the `Fixpoint` keyword to mark them explicitly and,
 - The recursive call can only be made on a subterm of the initial argument.
   i.e. at least one of the arguments of the recursive call must be a variable,
   and this variable must be reducing (e.g. through pattern matching).
**)

Fixpoint sum_n (n : nat) :=
  match n with
    0 => 0
  | S p => p + sum_n p

  end.

(*
Fixpoint rec_bad (n : nat) :=
  match n with
    0 => 0
  | S p => rec_bad (S p)

  end.
 *)

Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (s + p)

  end.

Fixpoint evenb (n : nat) : bool :=
  match n with
    0 => true
  | 1 => false
  | S (S p) => evenb p

  end.

Require Import List.

Check 1::2::3::nil.

Check list.
Check nil : list nat.
Eval compute in (1::2::3::nil ++ 4::nil).

Eval compute in map (fun x => x + 3) (1::2::3::nil).

(** Exercise on lists, map and app **)
Fixpoint to_n (n: nat) : list nat :=
  match n with
    0 => nil
  | S p => p :: to_n p

  end.

Eval compute in to_n 5.

Fixpoint sum_list l :=
  match l with
    nil => 0
  | p::rest => p + sum_list rest

  end.

Eval compute in sum_list (to_n 4).

Fixpoint insert n l :=
  match l with
    nil => n::nil
  | a::rest => if leb n a then n::l else a::(insert n rest)

  end.

Fixpoint sort l :=
  match l with
    nil => nil
  | a::rest => insert a (sort rest)

  end.

Eval compute in sort (4::2::3::1::nil).

(** Exercise on sorting **)
Definition first2_leb (l : list nat) : bool :=
  match l with
    a::b::_ => leb a b
  | _ => true

  end.

Eval compute in first2_leb nil.
Eval compute in first2_leb (1::nil).
Eval compute in first2_leb (1::2::nil).
Eval compute in first2_leb (3::2::nil).

Fixpoint is_sorted (l : list nat) : bool :=
  match l with
    nil => true
  | _::rest => if first2_leb l then is_sorted rest else false

  end.

Eval compute in is_sorted nil.
Eval compute in is_sorted (1::nil).
Eval compute in is_sorted (1::2::3::nil).
Eval compute in is_sorted (3::2::1::nil).

(** Exercise on counting **)
Fixpoint count_occur (n : nat) (l : list nat) : nat :=
  match l with
    nil => 0
  | a::rest => if beq_nat n a
               then 1 + count_occur n rest
               else count_occur n rest

  end.

Eval compute in count_occur 1 (1::2::3::1::nil).