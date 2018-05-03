Add LoadPath "/home/columpio/Docs/Coq/coq-supplementary/Bignums".
Add LoadPath "/home/columpio/Docs/Coq/coq-supplementary/".
Require Export Id.
Require Export State.
Require Export Bignums.BigZ.BigZ.

(* Type of binary operators *)
Inductive bop : Type :=
| Add : bop
| Sub : bop
| Mul : bop
| Div : bop
| Mod : bop
| Le  : bop
| Lt  : bop
| Ge  : bop
| Gt  : bop
| Eq  : bop
| Ne  : bop
| And : bop
| Or  : bop.

(* Type of arithmetic expressions *)
Inductive expr : Type :=
| Nat : nat -> expr
| Var : id  -> expr              
| Bop : bop -> expr -> expr -> expr.

(* Supplementary notation *)
Notation "x '[+]'  y" := (Bop Add x y) (at level 40, left associativity).
Notation "x '[-]'  y" := (Bop Sub x y) (at level 40, left associativity).
Notation "x '[*]'  y" := (Bop Mul x y) (at level 41, left associativity).
Notation "x '[/]'  y" := (Bop Div x y) (at level 41, left associativity).
Notation "x '[%]'  y" := (Bop Mod x y) (at level 41, left associativity).
Notation "x '[<=]' y" := (Bop Le  x y) (at level 39, no associativity).
Notation "x '[<]'  y" := (Bop Lt  x y) (at level 39, no associativity).
Notation "x '[>=]' y" := (Bop Ge  x y) (at level 39, no associativity).
Notation "x '[>]'  y" := (Bop Gt  x y) (at level 39, no associativity).
Notation "x '[==]' y" := (Bop Eq  x y) (at level 39, no associativity).
Notation "x '[/=]' y" := (Bop Ne  x y) (at level 39, no associativity).
Notation "x '[&]'  y" := (Bop And x y) (at level 38, left associativity).
Notation "x '[\/]' y" := (Bop Or  x y) (at level 38, left associativity).

Definition zbool (x : Z) : Prop := x = Z.one \/ x = Z.zero.
  
Definition zor (x y : Z) : Z :=
  if Z_le_gt_dec (Z.of_nat 1) (x + y) then Z.one else Z.zero.
   
Reserved Notation "[| e |] st => z" (at level 0).
Notation "st / x => y" := (st_binds Z st x y) (at level 0).

(* Denotational semantics *)
Inductive bs_eval : expr -> state Z -> Z -> Prop := 
  bs_Nat  : forall (s : state Z) (n : nat), [| Nat n |] s => (Z.of_nat n)
| bs_Var  : forall (s : state Z) (i : id) (z : Z), s / i => z -> [| Var i |] s => z

| bs_Add  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [+] b |] s => (za + zb)
| bs_Sub  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [-] b |] s => (za - zb)
| bs_Mul  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [*] b |] s => (za * zb)
| bs_Div  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [/] b |] s => (Z.div za zb)
| bs_Mod  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> [| a [%] b |] s => (Z.modulo za zb)

| bs_Le_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [<=] b |] s => Z.one
| bs_Le_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [<=] b |] s => Z.zero

| bs_Lt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [<] b |] s => Z.one
| bs_Lt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [<] b |] s => Z.zero

| bs_Ge_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.ge za zb -> [| a [>=] b |] s => Z.one
| bs_Ge_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.lt za zb -> [| a [>=] b |] s => Z.zero

| bs_Gt_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.gt za zb -> [| a [>] b |] s => Z.one
| bs_Gt_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.le za zb -> [| a [>] b |] s => Z.zero

| bs_Eq_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [==] b |] s => Z.one
| bs_Eq_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [==] b |] s => Z.zero

| bs_Ne_T : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> ~ Z.eq za zb -> [| a [/=] b |] s => Z.one
| bs_Ne_F : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> Z.eq za zb -> [| a [/=] b |] s => Z.zero

| bs_And  : forall (s : state Z) (a b : expr) (za zb : Z), 
             [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [&] b |] s => (za * zb)

| bs_Or   : forall (s : state Z) (a b : expr) (za zb : Z), 
              [| a |] s => za -> [| b |] s => zb -> zbool za -> zbool zb -> [| a [\/] b |] s => (zor za zb)
where "[| e |] st => z" := (bs_eval e st z). 

Hint Constructors bs_eval.

Module SmokeTest.

  Lemma nat_always : 
    forall (n : nat) (s : state Z), [| Nat n |] s => (Z.of_nat n).
  Proof. constructor. Qed.

  Lemma double_and_sum : 
    forall (s : state Z) (e : expr) (z : Z), 
      [| e [*] (Nat 2) |] s => z -> [| e [+] e |] s => z.
  Proof.
    intros. inversion_clear H. inversion_clear H1.
    assert (T: (za * Z.of_nat 2)%Z = (za + za)%Z).
    simpl. omega.
    rewrite T; auto.
  Qed.
  

End SmokeTest.

Reserved Notation "x ? e" (at level 0).

(* Set of variables is an expression *)
Inductive V : expr -> id -> Prop := 
  v_Var : forall (id : id), id ? (Var id)
| v_Bop : forall (id : id) (b : bop) (l r : expr), id ? l \/ id ? r -> id ? (Bop b l r)
(*| v_Add : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [+]  b)
| v_Sub : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [-]  b)
| v_Mul : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [*]  b)
| v_Div : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/]  b)
| v_Mod : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [%]  b)
| v_Le  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<=] b)
| v_Lt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [<]  b)
| v_Ge  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>=] b)
| v_Gt  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [>]  b)
| v_Eq  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [==] b)
| v_Ne  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [/=] b)
| v_And : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [&]  b)
| v_Or  : forall (id : id) (a b : expr), id ? a \/ id ? b -> id ? (a [\/] b)*)
where "x ? e" := (V e x).

(* If an expression is defined in some state, then each its' variable is
   defined in that state
*)
Lemma defined_expression: forall (e : expr) (s : state Z) (z : Z) (id : id),
  [| e |] s => z -> id ? e -> exists z', s / id => z'.
Proof.
  intros. generalize dependent z.
  induction e; intros.
  - inversion H0.
  - inversion H0. inversion_clear H. exists z. rewrite <- H1. assumption.
  - inversion_clear H; inversion_clear H0; inversion_clear H; eauto.
Qed.

(* If a variable in expression is undefined in some state, then the expression
   is undefined is that state as well
*)
Lemma undefined_variable: forall (e : expr) (s : state Z) (id : id),
  id ? e -> (forall (z : Z), ~ (s / id => z)) -> (forall (z : Z), ~ ([| e |] s => z)).
Proof. unfold not. intros. apply defined_expression with (id:=id) in H1.
       destruct H1. apply (H0 x). assumption. assumption. Qed. 

(* The evaluation relation is deterministic *)
Lemma bs_eval_deterministic: forall (e : expr) (s : state Z) (z1 z2 : Z),
  [| e |] s => z1 -> [| e |] s => z2 -> z1 = z2.
Proof. intros e s z1 z2 H1. generalize dependent z2. induction H1; intros.
       { inversion_clear H. reflexivity. }
       { inversion_clear H0. apply state_deterministic with (st:=s) (x:=i); assumption. }
       all: try (match goal with
                 | [ H : [| _ _ _ |] _ => _  |- _ ] => inversion_clear H
                 end).
       all: try (match goal with
                 | [ H0 : [|_|] _ => _, H1 : [|_|] _ => _ |- _ ] => apply IHbs_eval1 in H0; apply IHbs_eval2 in H1; subst
                end).
       all: try reflexivity.
       all: try omega.
       all: try (unfold not in *; exfalso; auto).
Qed.

                
(* Equivalence of states w.r.t. an identifier *)
Definition equivalent_states (s1 s2 : state Z) (id : id) :=
  forall z :Z, s1 / id => z <-> s2 / id => z.

Ltac bs_eval_constr :=
  try constructor;
  try (match goal with
       | [ |- [|(Bop ?Rel) _ _|] _ => Z.one ] =>
         match Rel with
         | Le => eapply bs_Le_T
         | Lt => eapply bs_Lt_T
         | Ge => eapply bs_Ge_T
         | Gt => eapply bs_Gt_T
         | Eq => eapply bs_Eq_T
         | Ne => eapply bs_Ne_T
         end
       | [ |- [|(Bop ?Rel) _ _|] _ => Z.zero ] =>
         match Rel with
         | Le => eapply bs_Le_F
         | Lt => eapply bs_Lt_F
         | Ge => eapply bs_Ge_F
         | Gt => eapply bs_Gt_F
         | Eq => eapply bs_Eq_F
         | Ne => eapply bs_Ne_F
         end
       end);
  eauto.
    

(* The result of expression evaluation in a state dependes only on the values
   of occurring variables
*)
Lemma variable_relevance: forall (e : expr) (s1 s2 : state Z) (z : Z),
  (forall (id : id), id ? e -> equivalent_states s1 s2 id) -> 
  [| e |] s1 => z -> [| e |] s2 => z.
Proof. unfold equivalent_states. intros. generalize dependent z.
       induction e; intros.
       - inversion_clear H0. constructor.
       - inversion_clear H0. apply bs_Var. apply H. constructor. auto.
       - inversion H0; subst a b0 s1 z; auto; bs_eval_constr.
         all: match goal with
              | [ IH : _ -> forall _, _ -> [|?e|] _ => _ |- [|?e|] _ => _ ] => apply IH; intros; auto; assert (H_bop: id ? (Bop b e1 e2)); try (apply v_Bop; tauto); specialize (H id H_bop z); auto
              end.
Qed.

(* Semantic equivalence *)
Reserved Notation "e1 '~~' e2" (at level 42, no associativity).

Inductive equivalent: expr -> expr -> Prop := 
  eq_intro : forall (e1 e2 : expr), 
               (forall (n : Z) (s : state Z), 
                 [| e1 |] s => n <-> [| e2 |] s => n
               ) -> e1 ~~ e2
where "e1 '~~' e2" := (equivalent e1 e2).

(* Semantic equivalence is an equivalence relation *)
Lemma eq_refl: forall (e : expr), e ~~ e.
Proof. intros. constructor; intros. tauto. Qed.

Lemma eq_symm: forall (e1 e2 : expr), e1 ~~ e2 -> e2 ~~ e1.
Proof. intros. constructor. inversion_clear H. intros. specialize (H0 n s). tauto. Qed.

Lemma eq_trans: forall (e1 e2 e3 : expr), e1 ~~ e2 -> e2 ~~ e3 -> e1 ~~ e3.
Proof. intros. inversion_clear H. inversion_clear H0. constructor; intros. specialize (H n s). specialize (H1 n s). tauto. Qed.

(* Contexts *)
Inductive Context : Type :=
| Hole : Context
| BopL : bop -> Context -> expr -> Context
| BopR : bop -> expr -> Context -> Context.

(* Plugging an expression into a context *)
Fixpoint plug (C : Context) (e : expr) : expr := 
  match C with
  | Hole => e
  | BopL b C e1 => Bop b (plug C e) e1
  | BopR b e1 C => Bop b (plug C e) e1
  end.  

Notation "C '<~' e" := (plug C e) (at level 43, no associativity).

(* Contextual equivalence *)
Reserved Notation "e1 '~c~' e2" (at level 42, no associativity).

Inductive contextual_equivalent: expr -> expr -> Prop :=
  ceq_intro : forall (e1 e2 : expr),
                (forall (C : Context), (C <~ e1) ~~ (C <~ e2)) -> e1 ~c~ e2
where "e1 '~c~' e2" := (contextual_equivalent e1 e2).

(* Contextual equivalence is equivalent to the semantic one *)
Lemma eq_eq_ceq: forall (e1 e2 : expr), e1 ~~ e2 <-> e1 ~c~ e2.
Proof. intros; split; intros.
       - constructor; intros. induction C; auto; simpl; constructor; intros; inversion_clear IHC;
               destruct b; split; intros; inversion_clear H1; bs_eval_constr; apply H0; auto.       
       - inversion_clear H. specialize (H0 Hole). auto. Qed.
