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


(** *Section 3* **)
Lemma example2 : forall a b : Prop, a /\ b -> b /\ a.

Proof.
  intros a b H.
  split.
  destruct H as [H1 H2].
  exact H2.
  intuition.
Qed.

Lemma example3 : forall a b : Prop, a \/ b -> b \/ a.

Proof.
  intros a b H.
  destruct H as [H1 | H1].
  right; assumption.
  left; assumption.
Qed.

Check le_S.
Check le_n.

(** **apply tactic** **)
(**
the tactic apply th replaces the current goal with n goals, whose statements are A1
a1 ... ak, . . . An a1 ... ak. This works well when all the variables that universally
quantified (here x1 . . . xn) appear in the goal conclusion.
**)

Lemma example4 : 3 <= 5.

Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.

Check le_trans.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.

Proof.
  intros x y xle10 yle10.
  apply le_trans with (m := 10).
  assumption.
  assumption.
Qed.

(** **rewrite tactic** **)
(**
Useful for equality theorems.

Most theorems are universally quantified and the values of the quantified variables
must be guessed when the theorems are used. The rewrite guesses the values of the
quantified variables by finding patterns of the left-hand side in the goal’s conclusion and
instanciating the variables accordingly.
**)

Lemma example6 : forall x y, (x + y) * (x + y) = x*x + 2*x*y + y*y.

SearchRewrite (_ * (_ + _)).
(** mult_plus_distr_l: forall n m p : nat, n * (m + p) = n * m + n * p **)

SearchRewrite ((_ + _) * _).
(** mult_plus_distr_r: forall n m p : nat, (n + m) * p = n * p + m * p **)

SearchRewrite ((_ + _) + _).
(** plus_assoc: forall n m p : nat, n + (m + p) = n + m + p **)

SearchPattern (?x * ?y = ?y * ?x).
(** mult_comm: forall n m : nat, n * m = m * n **)

SearchRewrite (S _ * _).
(** mult_1_l: forall n : nat, 1 * n = n **)
(** mult_succ_l: forall n m : nat, S n * m = n * m + m **)

SearchRewrite (_ * ( _ * _)).
(** mult_assoc: forall n m p : nat, n * (m * p) = n * m * p **)

Proof.
  intros x y.
  rewrite mult_plus_distr_l.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  rewrite plus_assoc.
  (* rewrite with a theorem from right to left, this is possible using the <- modifier. *)
  rewrite <- plus_assoc with (n := x*x).
  rewrite mult_comm with (n := y) (m := x).
  (* We want to rewrite only one of them with mult 1 l from right to left.
    This is possible, using a tactic called
    pattern to limit the place where rewriting occurs. *)
  pattern (x*y) at 1; rewrite <- mult_1_l.
  rewrite <- mult_succ_l.
  rewrite mult_assoc.
  reflexivity.
Qed.

(** **assert tactic** **)
(**
A common approach to proving difficult propositions is to assert intermediary steps using
a tactic called assert. Given an argument of the form (H : P), this tactic yields two
goals, where the first one is to prove P, while the second one is to prove the same statement
as before, but in a context where a hypothesis named H and with the statement P is added.
 **)

(** **auto tactics** **)
(**
intuition and tauto are often useful to prove facts that are tautologies in propositional logic
(try it whenever the proof only involves manipulations of conjunction, disjunction, and negation)

firstorder can be used for tautologies in first-order logic (try it when ever the proof only
involves the same connectives, plus existential and universal quantification)

auto is an extensible tactic that tries to apply a collection of theorems that were provided
beforehand by the user, eauto is like auto, it is more powerful but also more time-consuming.

ring mostly does proofs of equality for expressions containing addition and multiplication.
**)

(** **omega tactic** **)
(**
omega proves systems of linear inequations. An inequation is linear when it is of the form
A ≤ B or A < B, and A and B are sums of terms of the form n∗x.
**)

Require Import Omega.

Lemma omega_example : forall f x y, 0 < x -> 0 < f x -> 3* f x <= 2*y -> f x <= y.

Proof.
  intros; omega.
Qed.

(** **Tactic reference** **)
(**

|               | ->            | forall              | /\                    |
|---------------|---------------|---------------------|-----------------------|
| Hypothesis H  | apply H       | apply H             | elim H                |
|               |               |                     | case H                |
|               |               |                     | destruct H as [H1 H2] |
| Conclusion    | intros H      | intros H            | split                 |

|               | ~             | exists              | \/                    |
|---------------|---------------|---------------------|-----------------------|
| Hypothesis H  | elim H        | elim H              | elim H                |
|               | case H        | case H              | case H                |
|               |               | destruct H as [x H1]| destruct H as [H1|H2] |
| Conclusion    | intros H      | exists v            | left or right         |

|               | =             | False               |                       |
|---------------|---------------|---------------------|-----------------------|
| Hypothesis H  | rewrite <- H  | elim H              |                       |
|               | rewrite H     | case H              |                       |
| Conclusion    | reflexivity   |                     |                       |
|               | ring          |                     |                       |

**)


(** Exercise on logical connectives **)
Lemma exercise_lc_1 : forall a b c : Prop, a/\ (b/\c) -> (a/\b) /\c.
Proof.
  intros a b c H.
  destruct H as [H H1].
  destruct H1 as [H1 H2].
  split.
  split.
  assumption.
  assumption.
  assumption.
Qed.

Lemma exercise_lc_2 : forall a b c d : Prop, (a -> b) /\ (c -> d) /\ a /\ c -> b /\ d.
Proof.
  intros a b c d H.
  destruct H as [H1 [H2 [H3 H4]]].
  split.
  apply H1.
  assumption.
  apply H2.
  assumption.
Qed.

Lemma exercise_lc_3 : forall a : Prop, ~(a /\ ~a).
Proof.
  intros a H.
  elim H.
  destruct H as [H H1].
  elim H1.
  assumption.
Qed.

Lemma exercise_lc_4 : forall a b c : Prop, a \/ (b \/ c) -> (a \/ b) \/ c.
Proof.
  intros a b c H.
  destruct H as [H | [H1 | H2]].
  left; left; exact H.
  left; right; exact H1.
  right; exact H2.
Qed.

Lemma exercise_lc_5 : forall a b : Prop, (a \/ b) /\ ~a -> b.
Proof.
  intros a b H.
  destruct H as [[H | H1] H2].
  elim H2.
  assumption.
  assumption.
Qed.