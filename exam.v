(* Final Exam --- January 7, 2019 *)
Require Import Nat.
Require Import List.

Notation "[ ]" := nil. 
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).


Definition admit {T: Type} : T.  Admitted.


(* 1. Prove the following two facts about natural numbers. *)

Lemma mul_0_r : forall n : nat, n * 0 = 0.
Proof. 
   intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Lemma mul_1_r : forall n : nat, n * 1 = n.
Proof. 
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.


(* 2. Complete the following definition so that (div5 n) returns true 
iff n is divisible by 5. *)

Fixpoint div5 (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S(S O) => false
  | S(S(S O)) => false
  | S(S(S(S O))) => false
  | S(S(S(S(S O)))) => true
  | S(S(S(S(S n')))) => div5 n'
  end.

Example test1: div5 15 = true.
Proof. reflexivity. Qed.

Example test2: div5 23 = false.
Proof. reflexivity. Qed.


(* 3. Define a function createList such that (createList n) returns 
a list of n numbers from 2n to 1. *)


Fixpoint createList (n : nat) : list nat :=
  match n with
  | O => nil
  | S n' => (n+n)::(n+n-1)::createList n'
  end.

Example test3 : createList 4 = [8;7;6;5;4;3;2;1].
Proof. reflexivity. Qed. 


(* 4. (1) Define the relation gtodd between odd numbers such that 
   (gtodd m n) holds if and only if m is greater than n for odd numbers m and n.
(2) Show the transitivity of the relation gtodd. *)

(* lemmas *)
Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o E1 E2.
  induction E2.
  - apply E1.
  - apply le_S. apply IHE2 in E1. apply E1. Qed.

Theorem lt_trans: forall m n o, m < n -> n < o -> m < o.
Proof.
  unfold lt.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (m := (S n)) (n := (S m)) (o := o).
  apply Hnm.
  apply Hmo. Qed.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool   :=   negb (evenb n).
(* end of lemmas *)


Inductive gtodd : nat -> nat -> Prop :=
  | gt_odd : forall m n, (oddb m = true) /\ (oddb n = true) /\ n < m -> gtodd m n.
 
Example test4 : gtodd 3 1.
Proof.
  apply gt_odd. 
  split.
  - reflexivity.
  - split.
    + reflexivity.
    + unfold lt. apply le_S. apply le_n. Qed.

Example test5 : ~ (gtodd 4 3).
Proof.
  unfold not.
  intros.
  inversion H.
  destruct H0.
  inversion H0. Qed.

Theorem gtodd_trans : forall m n p,
  gtodd m n -> gtodd n p -> gtodd m p.
Proof.
  intros.
  inversion H. inversion H0.
  apply gt_odd. destruct H1. destruct H7.
  destruct H4. destruct H9.
  split.
  - apply H1.
  - split.
    + apply H9.
    + apply lt_trans with (m := p) (n := n) (o := m).
      * apply H10.
      * apply H8. Qed.

(* 5. Write a function (partition):

      partition : list nat -> list (list nat )

   which partitions a list into a list of 3 sublists. The first sublist
   contains all even numbers in the original list. The second sublist 
   contains all odd numbers divisible by 5 in the original list. The last 
   sublist contains all other elements. The order of elements in the
   three sublists should be the same as their order in the original list. 

   Hint: You can make use of the Coq function (filter).
*)

(* lemmas *)
Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.
(* end of lemmas *)

Definition partition (l : list nat) : list (list nat) :=
  [(filter evenb l); (filter div5 l); (filter (fun a=> andb (oddb a) (negb (div5 a))) l)].


Example test6: partition [1;2;3;9;4;5;6;15] = [[2;4;6]; [5;15]; [1;3;9]].
Proof. reflexivity. Qed.


(* 6. Prove that the excluded middle axiom implies the Peirce's law. *)

Theorem peirce : 
  (forall P, P \/ ~P) -> (forall P Q : Prop, ((P->Q)->P)->P).
Proof.
  intros.
  assert (P \/ ~P) as H1.
  apply H.
  inversion H1.
  - apply H2.
  - apply H0. intros. unfold not in H2. apply H2 in H3. inversion H3. Qed.
  


(* 7. Let a sequence of numbers F(n) be given as follows.
   F(0) = 0
   F(1) = 1
   F(2) = 1
   F(n) = F(n-1) + F(n-2) + F(n-3)   for n > 2.

Define the function Seq such that (Seq n) returns the sequence.

[0; F(0); 1; F(1); 2; F(2); 3; F(3); ... ; n; F(n)].
*)

(* lemmas *)
Fixpoint SeqNum (n: nat) : nat :=
  match n with
  | O => 0
  | S n' => match n' with
            | O => 1
            | S m => match m with
                     | O => 1
                     | S m' => SeqNum m' + SeqNum m + SeqNum n'
                     end
            end
  end.

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
(* end of lemmas *)

Fixpoint Seq (n: nat) : list nat :=
  match n with
  | O => [0; 0]
  | S n' => Seq n' ++ [n; SeqNum n]
  end.

Example test7 :  Seq 10 = 
[0; 0; 1; 1; 2; 1; 3; 2; 4; 4; 5; 7; 6; 13; 7; 24; 8; 44; 9; 81; 10; 149].
Proof. reflexivity. Qed.



(* 8. Consider the following type:

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Define a function taking as argument a natural number n
and a tree t and returning the number of occurrences of n in t.

Hint: You may use the function (eqb n m) which returns true iff the two natural
numbers n and m are equal.
*)

Inductive btree : Set :=
 | leaf : btree 
 | node : nat->btree->btree->btree.

Fixpoint occur (n: nat)(t: btree) : nat :=
  match t with
  | leaf => 0
  | node m b1 b2 => if eqb n m then 1+(occur n b1)+(occur n b2)
                    else (occur n b1)+(occur n b2)
  end.


Example test8 : occur 2 (node 1 (node 2 leaf (node 2 leaf leaf)) (node 3 (node 2 leaf leaf) leaf)) = 3.
Proof. reflexivity. Qed.


(* 9 Design a sorting algorithm which transforms a list of natural numbers into 
a list sorted in ascending oder. *)

(* lemmas *)
Fixpoint gea (n m: nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' =>false
         end
  | S n' => match m with
            | O => true
            | S m' => gea n' m'
            end
  end.

Fixpoint insert (n:nat)(l: list nat) : list nat :=  
  match l with
  | nil => n :: nil
  | h :: t => match gea n h with
              | true => n :: h :: t
              | false => h :: (insert n t)
              end
  end.

Fixpoint insertion_sort (l: list nat) : list nat := 
  match l with
  | nil => nil
  | h :: t => insert h (insertion_sort t)
  end.

Fixpoint rev (l:list nat) : list nat :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.
(* end of lemmas *)

Definition transform (l: list nat) : list nat :=
  rev (insertion_sort l).

Example test10 : transform [2;4;1;6;9;6;4;1;3;5;10] = [1;1;2;3;4;4;5;6;6;9;10].
Proof. reflexivity. Qed.

(* 10. The following definitions specify the abstract syntax of
    some arithmetic expressions and an evaluation function. *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

(* Suppose we define a function that takes an arithmetic expression 
   and slightly simplifies it, changing every occurrence of [e * 1] 
   (i.e., [(AMult e (ANum 1)]) into just [e]. *)

Fixpoint optimize_mult1 (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus e1 e2 => APlus (optimize_mult1 e1) (optimize_mult1 e2)
  | AMinus e1 e2 => AMinus (optimize_mult1 e1) (optimize_mult1 e2)
  | AMult e1 (ANum 1) => optimize_mult1 e1
  | AMult e1 e2 => AMult (optimize_mult1 e1) (optimize_mult1 e2)
  end.

(* Prove the following theorem that states the correctness of the 
optimization with respect to the evaluation of arithmetic expressions. *)

Theorem optimize_mult1_sound: forall a,
  aeval (optimize_mult1 a) = aeval a.
Proof.
  intros. induction a.
  - simpl. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - simpl. rewrite IHa1. rewrite IHa2. reflexivity.
  - destruct a2.
    + destruct n.
      * simpl. rewrite mul_0_r. symmetry. rewrite mul_0_r. reflexivity.
      * destruct n. simpl. rewrite mul_1_r. apply IHa1.
        simpl. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity. 
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity.
    + simpl. simpl in IHa2. rewrite IHa2. rewrite IHa1. reflexivity. Qed.
 
