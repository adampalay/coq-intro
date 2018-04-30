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

Search Nat.eqb.

Fixpoint list_n n :=
  match n with 
  0 => nil
  | S p => (list_n p)++p::nil
  end.

Compute list_n 5.


Definition is_sorted_head list :=
  match list with
    nil => true
  | a :: nil => true
  | a :: b :: tail => a <=? b
  end.

SearchPattern (bool -> bool -> bool).

Fixpoint is_sorted list :=
  match list with
    nil => true
  | a :: tail => andb (is_sorted_head list) (is_sorted tail)
  end.

Compute is_sorted (1::2::3::nil).
Compute is_sorted (1::2::3::1::nil).

Fixpoint count_occurrences list n :=
  match list with
    nil => 0
  | a :: tail => (if a =? n then 1 else 0) + (count_occurrences tail n)
  end.

Compute count_occurrences (1::2::3::nil) 2.
Compute count_occurrences (1::2::3::1::nil) 1.
Compute count_occurrences (1::2::3::nil) 4.

Lemma example2 : forall a b:Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split.
destruct H as [H1 H2].
exact H2.
destruct H as [H1 H2].
exact H1.
Qed.
(*intuition.
Qed.*)

Lemma example3 : forall A B, A \/ B -> B \/ A.
Proof.
intros A B H.
destruct H as [H1 | H1].
right.
(*exact H1.*)
assumption.
left ; assumption.
Qed.

Lemma example4 : 3 <= 5.
Proof.
apply le_S.
apply le_S.
apply le_n.
Qed.

Lemma example5 : forall x y, x <= 10 -> 10 <= y -> x <= y.
Proof.
intros x y x10 y10.
apply le_trans with (m := 10).
assumption.
assumption.
Qed.

