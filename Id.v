(** Borrowed from Pierce's "Software Foundations" *)

Require Import Arith Arith.EqNat.
Require Import Omega.

Inductive id : Type :=
  Id : nat -> id.

Reserved Notation "m <<= n" (at level 70, no associativity).
Reserved Notation "m >>  n" (at level 70, no associativity).
Reserved Notation "m <<  n" (at level 70, no associativity).

Inductive le_id : id -> id -> Prop :=
  le_conv : forall n m, n <= m -> (Id n) <<= (Id m)
where "n <<= m" := (le_id n m).   

Inductive lt_id : id -> id -> Prop :=
  lt_conv : forall n m, n < m -> (Id n) << (Id m)
where "n << m" := (lt_id n m).   

Inductive gt_id : id -> id -> Prop :=
  gt_conv : forall n m, n > m -> (Id n) >> (Id m)
where "n >> m" := (gt_id n m).   

Notation "n <<= m" := (le_id n m).
Notation "n >>  m" := (gt_id n m).
Notation "n <<  m" := (lt_id n m).

Lemma lt_eq_lt_id_dec: forall (id1 id2 : id), {id1 << id2} + {id1 = id2} + {id2 << id1}.
Proof.
  intros.
  destruct id1, id2.
  remember (lt_eq_lt_dec n n0).
  destruct s.
  - destruct s.
    + left. left. apply lt_conv. assumption.
    + left. right. rewrite <- e. reflexivity.
  - right. constructor. assumption.
Qed.


Lemma gt_eq_gt_id_dec: forall (id1 id2 : id), {id1 >> id2} + {id1 = id2} + {id2 >> id1}.
Proof. intros. destruct id1, id2. remember (gt_eq_gt_dec n n0).
       destruct s.
       - destruct s.
         + right. constructor. assumption.
         + left. right. rewrite e. reflexivity.
       - left. left. constructor. assumption.
Qed.


Lemma le_gt_id_dec : forall id1 id2 : id, {id1 <<= id2} + {id1 >> id2}.
Proof. intros. destruct id1, id2. remember (le_gt_dec n n0).
       destruct s.
       - left. constructor. assumption.
       - right. constructor. assumption.
Qed.

Lemma eq_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros.
  remember (Nat.eq_dec n m).
  assumption.
Qed.

Lemma eq_id_dec : forall id1 id2 : id, {id1 = id2} + {id1 <> id2}.
Proof.
  intros.
  destruct id1, id2.
  remember (eq_dec n n0).
  destruct s.
  - left. rewrite e. reflexivity.
  - right. unfold not in *. intro. apply n1. inversion H. reflexivity.
Qed.

Lemma eq_dec' : forall n m : nat, {n = m} + {n <> m}.
Proof.
  induction n; destruct m.
  - now left.
  - now right.
  - now right.
  - destruct (IHn m); [left|right]; auto.
Defined.


Lemma eq_id : forall (T:Type) x (p q:T), (if eq_id_dec x x then p else q) = p.
Proof. intros. destruct (eq_id_dec x x); tauto. Qed.

Lemma neq_id : forall (T:Type) x y (p q:T), x <> y -> (if eq_id_dec x y then p else q) = q. 
Proof. intros. destruct (eq_id_dec x y); tauto. Qed.

Lemma lt_gt_id_false : forall id1 id2 : id, id1 >> id2 -> id2 >> id1 -> False.
Proof. destruct id1, id2. intros. inversion_clear H. inversion_clear H0. omega. Qed.

Lemma le_gt_id_false : forall id1 id2 : id, id2 <<= id1 -> id2 >> id1 -> False.
Proof. destruct id1, id2. intros. inversion_clear H. inversion_clear H0. omega. Qed.

Lemma le_lt_eq_id_dec : forall id1 id2 : id, id1 <<= id2 -> {id1 = id2} + {id2 >> id1}.
Proof. destruct id1, id2. intros. destruct (le_lt_eq_dec n n0).
       inversion_clear H. assumption. right. apply gt_conv. omega.
       left. rewrite e. reflexivity. Qed.

Lemma neq_lt_gt_id_dec : forall id1 id2 : id, id1 <> id2 -> {id1 >> id2} + {id2 >> id1}.
Proof. intros. destruct (gt_eq_gt_id_dec id1 id2); tauto. Qed.
    
Lemma eq_gt_id_false : forall id1 id2 : id, id1 = id2 -> id1 >> id2 -> False.
Proof. intros. subst. inversion_clear H0. omega. Qed.