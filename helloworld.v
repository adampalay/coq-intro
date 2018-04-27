Require Import Bool.
Require Import Arith.
Require Import List.



Compute if true then 3 else 5.

Check 0.
Definition double (n : nat) := plus n n.
Check S 0.

Check double (S 0).
Compute double (S 0).


Definition is_zero (n : nat) :=
  match n with
    0 => true
  | S _ => false
  end.

Compute is_zero 0.
Compute is_zero (S 0).

Print pred.
Print Init.Nat.pred.

Fixpoint sum_n n := 
  match n with
    0 => 0
  | S p => p + sum_n p
  end. 

Fixpoint sum_n2 n s :=
  match n with
    0 => s
  | S p => sum_n2 p (p + s)
  end.



