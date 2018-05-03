Require Import List.
Import ListNotations.
Require Import Omega.

Add LoadPath "/home/columpio/Docs/Coq/coq-supplementary/Bignums".
Add LoadPath "/home/columpio/Docs/Coq/coq-supplementary/".
Require Export Bignums.BigZ.BigZ.
Require Export Id.
Require Export State.
Require Export Expr.

(* The type of statements *)
Inductive stmt : Type :=
  | SKIP  : stmt
  | Assn  : id -> expr -> stmt
  | READ  : id -> stmt
  | WRITE : expr -> stmt
  | Seq   : stmt -> stmt -> stmt
  | If    : expr -> stmt -> stmt -> stmt
  | While : expr -> stmt -> stmt.

(* Supplementary notation *)
Notation "x  '::=' e"                         := (Assn  x e    ) (at level 37, no associativity).
Notation "s1 ';;'  s2"                        := (Seq   s1 s2  ) (at level 35, right associativity).
Notation "'COND' e 'THEN' s1 'ELSE' s2 'END'" := (If    e s1 s2) (at level 36, no associativity).
Notation "'WHILE' e 'DO' s 'END'"             := (While e s    ) (at level 36, no associativity).

(* Configuration *)
Definition conf :=  (state Z * list Z * list Z)%type.

Reserved Notation "c1 '==' s '==>' c2" (at level 0).

(* Big-step evaluation relation *)
Notation "st [ x '<-' y ]" := (update Z st x y) (at level 0).

Inductive bs_int : stmt -> conf -> conf -> Prop := 
  | bs_Skip        : forall (c : conf), c == SKIP ==> c 
  | bs_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == x ::= e ==> (s [x <- z], i, o)
  | bs_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                       (s, z::i, o) == READ x ==> (s [x <- z], i, o)
  | bs_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) == WRITE e ==> (s, i, z::o)
  | bs_Seq         : forall (c c' c'' : conf) (s1 s2 : stmt),
                       c == s1 ==> c' -> c' == s2 ==> c'' -> c ==  s1 ;; s2 ==> c''
  | bs_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.one -> (s, i, o) == s1 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (e : expr) (s1 s2 : stmt),
                       [| e |] s => Z.zero -> (s, i, o) == s2 ==> c' -> (s, i, o) == COND e THEN s1 ELSE s2 END ==> c'
  | bs_While_True  : forall (st : state Z) (i o : list Z) (c' c'' : conf) (e : expr) (s : stmt),
                       [| e |] st => Z.one -> (st, i, o) == s ==> c' -> c' == WHILE e DO s END ==> c'' ->
                          (st, i, o) == WHILE e DO s END ==> c''
  | bs_While_False : forall (st : state Z) (i o : list Z) (e : expr) (s : stmt),
                       [| e |] st => Z.zero -> (st, i, o) == WHILE e DO s END ==> (st, i, o)
where "c1 == s ==> c2" := (bs_int s c1 c2).

(* Big-step semantics is deterministic *)
Lemma bs_int_deterministic : forall (c c1 c2 : conf) (s : stmt), c == s ==> c1 -> c == s ==> c2 -> c1 = c2.
Proof. intros. generalize dependent c2. induction H; intros c2 H_; inversion_clear H_; unfold update.
       all: try (match goal with
                 | [ H1: [|?e|] ?s => _, H2: [|?e|] ?s => ?z |- _ ] => apply bs_eval_deterministic with (z1:=z) in H1; subst
                 end).
       all: auto.
       all: try (match goal with
                 | [ H: Z.zero = Z.one |- _ ] => inversion H
                 | [ H: Z.one = Z.zero |- _ ] => inversion H
                 end).
       - apply IHbs_int2. apply IHbs_int1 in H1; subst. auto.
       - apply IHbs_int2. apply IHbs_int1 in H3; subst. auto.
Qed.

Reserved Notation "s1 '~~~' s2" (at level 0).

Inductive bs_equivalent: stmt -> stmt -> Prop :=
  bs_eq_intro: forall (s1 s2 : stmt), 
                 (forall (c c' : conf), c == s1 ==> c' <-> c == s2 ==> c') -> s1 ~~~ s2
where "s1 '~~~' s2" := (bs_equivalent s1 s2).

Module SmokeTest.

  Lemma seq_assoc : forall (s1 s2 s3 : stmt) (c c' : conf),
    ((s1 ;; s2) ;; s3) ~~~ (s1 ;; (s2 ;; s3)).
  Proof. intros. constructor. intros. split; intros.
         all: try (repeat match goal with
                   | [ H: _ == _ ;; _ ==> _ |- _ ] => inversion_clear H
                   end).
         all: repeat (eapply bs_Seq; eauto). Qed.

  Lemma while_unfolds : forall (e : expr) (s : stmt),
                          (WHILE e DO s END) ~~~ (COND e THEN s ;; WHILE e DO s END ELSE SKIP END).
  Proof. intros. constructor; intros; split; intros; inversion_clear H.
         - apply bs_If_True; auto. eapply bs_Seq; eauto.
         - apply bs_If_False; auto. apply bs_Skip.
         - inversion_clear H1. eapply bs_While_True; eauto.
         - inversion_clear H1. apply bs_While_False. auto. Qed.
  
  Lemma while_false : forall (e : expr) (s : stmt) (st : state Z) (i o : list Z) (c : conf),
                        c == WHILE e DO s END ==> (st, i, o) -> [| e |] st => Z.zero.
  Proof. intros. admit. Admitted.

  Definition True := Nat 1.

  Lemma loop_eq_undefined : (WHILE True DO SKIP END) ~~~ (COND (Nat 3) THEN SKIP ELSE SKIP END).
  Proof. apply bs_eq_intro; intros; split; intro; exfalso.
         - remember (while_unfolds True SKIP). inversion_clear b. apply H0 in H. admit.
         - inversion_clear H; inversion H0. Admitted.
  
End SmokeTest.

(* Contextual equivalence *)
Inductive Context : Type :=
| Hole 
| SeqL   : Context -> stmt -> Context
| SeqR   : stmt -> Context -> Context
| IfThen : expr -> Context -> stmt -> Context
| IfElse : expr -> stmt -> Context -> Context
| WhileC : expr -> Context -> Context.

(* Plugging a statement into a context *)
Fixpoint plug (C : Context) (s : stmt) : stmt := 
  match C with
  | Hole => s
  | SeqL     C  s1 => Seq (plug C s) s1
  | SeqR     s1 C  => Seq s1 (plug C s) 
  | IfThen e C  s1 => If e (plug C s) s1
  | IfElse e s1 C  => If e s1 (plug C s)
  | WhileC   e  C  => While e (plug C s)
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: stmt -> stmt -> Prop :=
  ceq_intro : forall (s1 s2 : stmt),
                (forall (C : Context), (C <~ s1) ~~~ (C <~ s2)) -> s1 ~c~ s2
where "s1 '~c~' s2" := (contextual_equivalent s1 s2).

Lemma while_wrap : forall (s1 s2 : stmt) (e : expr), s1 ~~~ s2 -> WHILE e DO s1 END ~~~ WHILE e DO s2 END.
Proof. intros. inversion_clear H. constructor; intros. split; intro. admit. Admitted.

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (s1 s2 : stmt), s1 ~~~ s2 <-> s1 ~c~ s2.
Proof. intros. split; intros.
       - constructor. intros.
         induction C; simpl; auto; constructor; split; intros.
         all: try (inversion_clear H0).
         all: try (match goal with
                   | [ H : [|_|] _ => (Z.one) |- _ == COND _ THEN _ ELSE _ END ==> _ ] => apply bs_If_True
                   | [ H : [|_|] _ => (Z.zero) |- _ == COND _ THEN _ ELSE _ END ==> _ ] => apply bs_If_False
                   | [ H : [|_|] _ => (Z.one) |- _ == WHILE _ DO _ END ==> _ ] => apply bs_While_True with (c':=c'0)
                   | [ H : [|_|] _ => (Z.zero) |- _ == WHILE _ DO _ END ==> _ ] => apply bs_While_False
                   | [ |- _ == _ ;; _ ==> _ ] => apply (bs_Seq c c'0 c')
                   end).
         all: try (inversion_clear IHC; apply H0).
         all: auto.
         all: (remember (while_wrap (C <~ s1) (C <~ s2) e IHC); inversion_clear b; specialize (H0 c'0 c')).
         + rewrite <- H0. auto.
         + rewrite H0. auto.
       - inversion_clear H. specialize (H0 Hole). simpl in H0. assumption. Qed.

Module SS_Semantics.
Reserved Notation "c1 -- s --> c2" (at level 0).

Inductive ss_int_step : stmt -> conf -> option stmt * conf -> Prop :=
| ss_Skip        : forall (c : conf), c -- SKIP --> (None, c) 
| ss_Assign      : forall (s : state Z) (i o : list Z) (x : id) (e : expr) (z : Z), 
                       [| e |] s => z -> (s, i, o) -- x ::= e --> (None, (s [x <- z], i, o))
| ss_Read        : forall (s : state Z) (i o : list Z) (x : id) (z : Z),
                       (s, z::i, o) -- READ x --> (None, (s [x <- z], i, o))
| ss_Write       : forall (s : state Z) (i o : list Z) (e : expr) (z : Z), 
    [| e |] s => z -> (s, i, o) -- WRITE e --> (None, (s, i, z::o))
| ss_Seq_Compl   : forall (c c' : conf) (s1 s2 : stmt), c -- s1 --> (None, c') -> c -- s1 ;; s2 --> (Some s2, c')
| ss_Seq_InCompl : forall (c c' : conf) (s1 s2 s1' : stmt), c -- s1 --> (Some s1', c') -> c -- s1 ;; s2 --> (Some (s1' ;; s2), c')
| ss_If_True     : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr), [| e |] s => Z.one -> (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s1, (s, i, o))

| ss_If_False    : forall (s : state Z) (i o : list Z) (s1 s2 : stmt) (e : expr), [| e |] s => Z.zero -> (s, i, o) -- COND e THEN s1 ELSE s2 END --> (Some s2, (s, i, o))
| ss_While : forall (c : conf) (s : stmt) (e : expr), c -- WHILE e DO s END --> (Some (COND e THEN s ;; WHILE e DO s END ELSE SKIP END), c)
where "c1 -- s --> c2" := (ss_int_step s c1 c2).

Reserved Notation "c1 '--' s '-->>' c2" (at level 0).

Inductive ss_int : stmt -> conf -> conf -> Prop :=
| ss_int_Base : forall (s : stmt) (c c' : conf), c -- s --> (None, c') -> c -- s -->> c'
| ss_int_Step : forall (s s' : stmt) (c c' c'' : conf), c -- s --> (Some s', c') -> c' -- s' -->> c'' -> c -- s -->> c''
where "c1 -- s -->> c2" := (ss_int s c1 c2).

Lemma ss_int_step_deterministic : forall (c : conf) (c' c'' : option stmt * conf) (s : stmt), c -- s --> c' -> c -- s --> c'' -> c' = c''.
Proof. intros. generalize dependent c. generalize dependent c'. generalize dependent c''. induction s; intros.
       all: try (inversion H; inversion H0; auto; subst).
       all: try (match goal with
                 | [ H : (_, _, _) = (_, _, _) |- _ ] => inversion H; subst
                 end).
       all: try (match goal with
                 | [ H1 : [|_|] _ => ?z, H2 : [|_|] _ => ?z' |- _ ] => apply bs_eval_deterministic with (z2:=z') in H1; subst
                 end).
       all: auto.
       all: try (inversion H6).
       all: try (match goal with
                 | [ H5 : ?c -- ?s1 --> _, H10: ?c -- ?s1 --> ?c2 |- _ ] => apply IHs1 with (c':=c2) in H5; auto
                 end).
       all: inversion H5; auto.
Qed.
         
Lemma ss_int_deterministic : forall (c c' c'' : conf) (s : stmt), c -- s -->> c' -> c -- s -->> c'' -> c' = c''.
Proof. intros. generalize dependent c'. induction H0; intros.
       - inversion_clear H0.
         + apply ss_int_step_deterministic with (c' := (None, c')) in H1. inversion H1. auto. auto.
         + apply ss_int_step_deterministic with (c' := (None, c')) in H1. inversion H1. auto.
       - apply IHss_int. inversion_clear H1.
         + apply ss_int_step_deterministic with (c' := (Some s', c')) in H2. inversion H2. auto.
         + apply ss_int_step_deterministic with (c' := (Some s'0, c'1)) in H. inversion H. subst. auto. auto.
Qed.

Lemma ss_composition : forall (c c' c'' : conf) (s1 s2 : stmt), c -- s1 -->> c'' -> c'' -- s2 -->> c' -> c -- s1 ;; s2 -->> c'.
Proof. intros. induction H.
       + eapply ss_Seq_Compl in H. eapply ss_int_Step; eauto.
       + specialize (IHss_int H0). eapply ss_Seq_InCompl in H. eapply ss_int_Step; eauto.
Qed.

Lemma bs_ss_single_step : forall (s : stmt) (c c' : conf), c -- s --> (None, c') -> c == s ==> c'.
Proof. intros. inversion_clear H; constructor; auto. Qed.

Lemma ss_bs_composition : forall (c c' c'' : conf) (s s' : stmt), c -- s --> (Some s', c') -> c' == s' ==> c'' -> c == s ==> c''.
Proof. intros. generalize dependent c. generalize dependent c''. generalize dependent c'. generalize dependent s'. induction s; intros; inversion H; subst.
       - apply bs_ss_single_step in H4. eapply bs_Seq; eauto.
       - inversion_clear H0.
         eapply IHs1 in H1; eauto.
         eapply bs_Seq; eauto.
       - apply bs_If_True; auto.
       - apply bs_If_False; auto.
       - remember (SmokeTest.while_unfolds e s). inversion_clear b. apply H1. auto. Qed.

Theorem bs_ss_eq : forall (s : stmt) (c c' : conf), c == s ==> c' <-> c -- s -->> c'.
Proof. intros. split; intros.
       - induction H.
         all: try (constructor; constructor; auto).
         + eapply ss_composition; eauto.
         + eapply ss_int_Step; eauto. apply ss_If_True. auto.
         + eapply ss_int_Step; eauto. apply ss_If_False. auto.
         + eapply ss_int_Step. apply ss_While. eapply ss_int_Step. apply ss_If_True; auto.
           eapply ss_composition; eauto.
         + eapply ss_int_Step. apply ss_While. eapply ss_int_Step. apply ss_If_False; auto.
           apply ss_int_Base. apply ss_Skip.
       - induction H.
         + apply bs_ss_single_step; auto.
         + eapply ss_bs_composition; eauto.
 Qed.

End SS_Semantics.

(* CPS-style semantics *)
Inductive cont : Type := 
| KEmpty : cont
| KStmt  : stmt -> cont.
 
Definition app (l r : stmt) : stmt :=
  match (l, r) with
  | (SKIP, _) => r
  | (_, SKIP) => l
  | (_, _) => l ;; r
  end.

Notation "s1 @ s2" := (app s1 s2) (at level 0).

Reserved Notation "k '|-' c1 '--' s '-->' c2" (at level 0).

Inductive cps_int : stmt -> stmt -> conf -> conf -> Prop :=
| cps_Empty       : forall (c : conf), SKIP |- c -- SKIP --> c
| cps_Skip        : forall (c c' : conf) (k : stmt), 
                      SKIP |- c -- k --> c' -> 
                      k |- c -- SKIP --> c'
| cps_Assn        : forall (s : state Z) (i o : list Z) (c' : conf) (k : stmt) (x : id) (e : expr) (n : Z),
                      [| e |] s => n ->
                      SKIP |- (s [x <- n], i, o) -- k --> c' ->
                      k |- (s, i, o) -- (x ::= e) --> c'
| cps_Read        : forall (s : state Z) (i o : list Z) (c' : conf) (k : stmt) (x : id) (z : Z),
                      SKIP |- (s [x <- z], i, o) -- k --> c' ->
                      k |- (s, z::i, o) -- (READ x) --> c'
| cps_Write       : forall (s : state Z) (i o : list Z) (c' : conf) (k : stmt) (e : expr) (z : Z),
                      [| e |] s => z ->
                      SKIP |- (s, i, z::o) -- k --> c' ->
                      k |- (s, i, o) -- (WRITE e) --> c'
| cps_Seq         : forall (c c' : conf) (k : stmt) (s1 s2 : stmt), 
                      s2 @ k |- c -- s1 --> c' ->
                      k |- c -- (s1 ;; s2) --> c'
| cps_If_True     : forall (s : state Z) (i o : list Z) (c' : conf) (k : stmt) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.one ->
                      k |- (s, i, o) -- s1 --> c' ->
                      k |- (s, i, o) -- (COND e THEN s1 ELSE s2 END) --> c'
| cps_If_False    : forall (s : state Z) (i o : list Z) (c' : conf) (k : stmt) (e : expr) (s1 s2 : stmt),
                      [| e |] s => Z.zero ->
                      k |- (s, i, o) -- s2 --> c' ->
                      k |- (s, i, o) -- (COND e THEN s1 ELSE s2 END) --> c'
| cps_While_True  : forall (st : state Z) (i o : list Z) (c' : conf) (k : stmt) (e : expr) (s : stmt),
                      [| e |] st => Z.one ->
                      (WHILE e DO s END) @ k |- (st, i, o) -- s --> c' ->
                      k |- (st, i, o) -- (WHILE e DO s END) --> c'
| cps_While_False : forall (st : state Z) (i o : list Z) (c' : conf) (k : stmt) (e : expr) (s : stmt),
                      [| e |] st => Z.zero ->
                      SKIP |- (st, i, o) -- k --> c' ->
                      k |- (st, i, o) -- (WHILE e DO s END) --> c'
where "k |- c1 -- s --> c2" := (cps_int k s c1 c2).

Lemma cps_bs_gen : forall (s : stmt) (c c' : conf) (s1 k : stmt), k |- c -- s1 --> c' -> s = s1 @ k -> c == s ==> c'.
Proof. admit. Admitted.

Lemma SKIP_app_zero_r : forall (k : stmt), k @ SKIP = k.
Proof. intros. destruct k; auto. Qed.

Lemma SKIP_app_zero_l : forall (k : stmt), SKIP @ k = k.
Proof. intros. destruct k; auto. Qed.

Lemma swap_SKIP : forall (k : stmt), k @ SKIP = SKIP @ k.
Proof. intros. destruct k; auto. Qed.

Lemma K_semicolon_assoc : forall (s s1 s2 s3 : stmt) (c c' : conf), ((s1 ;; s2) ;; s3) |- c -- s --> c' -> (s1 ;; (s2 ;; s3)) |- c -- s --> c'.
Proof. admit. Admitted.

Lemma K_app_assoc : forall (s s1 s2 s3 : stmt) (c c' : conf), (s1 @ s2) @ s3 |- c -- s --> c' -> s1 @ (s2 @ s3) |- c -- s --> c'.
Proof. intros. destruct s1; solve [
       rewrite SKIP_app_zero_l in *; assumption
       | destruct s2; solve [
         rewrite SKIP_app_zero_r in H; rewrite SKIP_app_zero_l; auto
         | destruct s3; solve [
           rewrite SKIP_app_zero_r in H; rewrite SKIP_app_zero_r; auto
           | unfold app in *; apply K_semicolon_assoc; auto]]]. Qed.

Lemma app_step : forall (s1 s2 : stmt) (c c' : conf), s2 |- c -- s1 --> c' -> SKIP |- c -- s1 @ s2 --> c'.
Proof. intros. destruct s1; solve [
       rewrite SKIP_app_zero_l; destruct s2; auto; inversion_clear H; auto
       | destruct s2; unfold app; auto; constructor; rewrite SKIP_app_zero_r; auto ]. Qed.
         
Lemma cps_composition : forall (k : stmt) (s1 s2 : stmt) (c c' c'' : conf), k |- c -- s1 --> c' -> SKIP |- c' -- s2 --> c'' -> (k @ s2) |- c -- s1 --> c''.
Proof. intros. induction H.
       - unfold app. apply cps_Skip. assumption.
       - constructor. apply app_step. apply IHcps_int in H0. rewrite SKIP_app_zero_l in H0. assumption.
       - econstructor; eauto; apply IHcps_int in H0; rewrite SKIP_app_zero_l in H0; apply app_step in H0; auto.
       - econstructor; eauto; apply IHcps_int in H0; rewrite SKIP_app_zero_l in H0; apply app_step in H0; auto.
       - econstructor; eauto; apply IHcps_int in H0; rewrite SKIP_app_zero_l in H0; apply app_step in H0; auto.
       - econstructor; eauto; apply IHcps_int in H0. apply K_app_assoc. assumption.
       - constructor; auto.
       - apply cps_If_False; auto.
       - constructor; auto. apply IHcps_int in H0. apply K_app_assoc. assumption.
       - apply cps_While_False; auto. apply IHcps_int in H0. unfold app in H0. apply app_step. assumption. Qed.

Lemma bs_int_to_cps_int: forall (c c' : conf) (s : stmt), c == s ==> c' -> SKIP |- c -- s --> c'.
Proof. intros. induction H; intros.
       - constructor; constructor.
       - eapply cps_Assn; eauto. apply cps_Empty.
       - eapply cps_Read; eauto. apply cps_Empty.
       - eapply cps_Write; eauto. apply cps_Empty.
       - constructor. rewrite swap_SKIP. eapply cps_composition; eauto.
       - apply cps_If_True; auto.
       - apply cps_If_False; auto.
       - apply cps_While_True; auto. rewrite swap_SKIP. eapply cps_composition; eauto.
       - apply cps_While_False; auto. constructor. Qed.

Lemma cps_int_to_bs_int: forall (st : state Z) (i o : list Z) (c' : conf) (s : stmt),
  SKIP |- (st, i, o) -- s --> c' -> (st, i, o) == s ==> c'.
Proof. admit. Admitted.
