(** Based on Benjamin Pierce's "Software Foundations" *)

Require Import List.
Import ListNotations.
Require Import Omega.
Require Export Arith Arith.EqNat.
Require Export Id.

Section S.

  Variable A : Set.

  Definition state := list (id * A). 

  Reserved Notation "st / x => y" (at level 0).

  Inductive st_binds : state -> id -> A -> Prop := 
    st_binds_hd : forall st id x, ((id, x) :: st) / id => x
  | st_binds_tl : forall st id x id' x', id <> id' -> st / id => x -> ((id', x')::st) / id => x
  where "st / x => y" := (st_binds st x y).

  Definition update (st : state) (id : id) (a : A) : state := (id, a) :: st.

  Lemma eq_id_symm : forall (x y : id), x <> y -> y <> x.
  Proof. unfold not. intros. apply H. symmetry. assumption. Qed.
  
  Notation "st [ x '<-' y ]" := (update st x y) (at level 0).

  Lemma falso_a_neq_a : forall (x : id), x <> x -> False.
  Proof. unfold not. intros. apply H. reflexivity. Qed.
  
  Lemma st_binds_tl_inv : forall st id x id' x', id <> id' -> ((id', x')::st) / id => x -> st / id => x.
  Proof. intros. inversion H0. subst. exfalso. apply falso_a_neq_a with (x:=id). assumption.
         assumption. Qed.
  
  Lemma state_deterministic: forall (st : state) (x : id) (n m : A),
    st / x => n -> st / x => m -> n = m.
  Proof. intros st x n m H. generalize dependent m. induction H.
         - intros. inversion_clear H. reflexivity. unfold not in H0. exfalso. apply H0. reflexivity.
         - intros. apply IHst_binds. apply st_binds_tl_inv in H1; assumption. Qed.

  Lemma update_eq : forall (st : state) (x : id) (n : A),
    st [x <- n] / x => n.
  Proof. intros. unfold update. apply st_binds_hd. Qed.

  Lemma update_neq : forall (st : state) (x2 x1 : id) (n m : A),
    x2 <> x1 -> st / x1 => m -> st [x2 <- n] / x1 => m.
  Proof. intros. unfold update. apply st_binds_tl. apply eq_id_symm. assumption. assumption. Qed.

  Lemma update_shadow : forall (st : state) (x1 x2 : id) (n1 n2 m : A),
    st[x2 <- n1][x2 <- n2] / x1 => m -> st[x2 <- n2] / x1 => m.
  Proof. unfold update. intros. inversion H; subst.
         - apply st_binds_hd.
         - apply st_binds_tl. assumption. apply st_binds_tl_inv in H6; assumption. Qed.

  Lemma update_same : forall (st : state) (x1 x2 : id) (n m : A),
    st / x1 => n -> st / x2 => m -> st [x1 <- n] / x2 => m.
  Proof. intros. unfold update. destruct (eq_id_dec x1 x2); subst.
         - assert (Hnm: n = m).
           { apply state_deterministic with (st:=st) (x:=x2); assumption. }
           subst. apply st_binds_hd.
         - apply st_binds_tl. apply eq_id_symm. assumption. assumption. Qed.

  Lemma update_eq' : forall (st : state) (x : id) (n m : A), st [x <- n] / x => m -> n = m.
  Proof. unfold update. intros. apply state_deterministic with (st:=(x, n)::st) (x:=x).
         - apply st_binds_hd.
         - assumption. Qed.
  
  Lemma update_permute : forall (st : state) (x1 x2 x3 : id) (n1 n2 m : A),
    x2 <> x1 -> 
    st [x2 <- n1][x1 <- n2] / x3 => m ->
    st [x1 <- n2][x2 <- n1] / x3 => m.
  Proof. unfold update. intros. destruct (eq_id_dec x3 x1); subst.
         - apply update_eq' in H0. subst. apply st_binds_tl.
           + apply eq_id_symm. assumption.
           + apply st_binds_hd.
         - destruct (eq_id_dec x2 x3); subst.
           + apply st_binds_tl_inv in H0.
             * apply update_eq' in H0. subst. apply st_binds_hd.
             * assumption.
           + apply st_binds_tl_inv in H0. apply st_binds_tl_inv in H0.
             apply st_binds_tl. apply eq_id_symm. assumption.
             apply st_binds_tl. assumption. assumption. apply eq_id_symm. assumption. assumption. Qed.

End S.