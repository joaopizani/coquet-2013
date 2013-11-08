(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

(** definition of finite types (types with a duplicate free enumeration) *)


Require Import Bool Arith Omega. 
Require Import EqT Common. 


Notation "[ :: ]" := nil (at level 0, format "[ :: ]") : list_scope.

(* Notation "x :: s" := (cons x s) *)
(*   (at level 60, right associativity, format "x :: s") : list_scope. *)

Notation "[ :: x ]" := (cons x nil)
  (at level 0,  format "[ :: x ]") : list_scope.

Notation "[ :: x1 ; .. ; xn ]" := (x1 ::  .. (xn :: nil) ..)%list
  (at level 0, format "[ :: '[' x1 ; '/' .. ; '/' xn ']' ]" ) : list_scope.

Section list.
  Context `{eqT}.
  Open Scope list_scope.
  Variable pred : A -> bool.
  Fixpoint count  (l : list A) : nat  :=
    match l with 
      | [ :: ] => 0
      | x :: q => if pred x then 1 + count q else count q
    end.
  Fixpoint mem e ( l : list A) : bool :=
    match l with 
      | [ :: ] => false
      | x :: q => if equal e x  then true else mem e q
    end.
  Lemma count_app l l' : count  (l ++ l') = count l + count l'. 
  Proof.
    induction l; simpl; [|case (pred a); rewrite IHl]; reflexivity.  
  Qed.
End list.
Section count. 
  Context {A B : Type }{eqA : eqT A} {eqB : eqT B}.
  Variable predA : A -> bool.
  Variable predB : B -> bool.
  Hypothesis f : A -> B. 
  Hypothesis Hf : (forall a : A, predA a = predB (f a)).
  Lemma count_map l : 
    count predB (List.map f l) = count predA l . 
  Proof. 
    induction l. 
    simpl. auto. 
    simpl. 
    rewrite Hf. 
    case (predB (f a)).
    rewrite IHl. reflexivity. 
    auto. 
  Qed.

End count. 



Unset Implicit Arguments. 
Class Fin A := 
  {
    eq_fin : eqT A;
    enum : list A;
    axiom : forall (x : A), count (equal x) enum = 1 
  }.



Notation "#| A |" := (List.length (enum A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Implicit Arguments enum [Fin]. 

Notation "#| A |" := (List.length (enum A))
  (at level 0, A at level 99, format "#| A |") : nat_scope.

Section Fin_zero.
  
  Definition enum_zero : list zero := nil. 
  Lemma axiom_zero :   forall x : zero, count (equal x) enum_zero = 1.
  Proof. intros []; reflexivity. Qed.
  Global Instance Fin_zero : Fin zero :=
    {
      eq_fin := eqT_zero;
      enum := enum_zero;
      axiom := axiom_zero
    }.
End Fin_zero. 

Section Fin_unit. 
  Definition enum_unit : list unit := cons tt nil.
  Lemma axiom_unit :   forall x : unit, count (equal x) enum_unit = 1.
  Proof. intros []; reflexivity. Qed.
  Global Instance Fin_unit : Fin unit := 
  {| 
    eq_fin := eqT_unit;
    enum := enum_unit;
    axiom := axiom_unit
  |}.
End Fin_unit.

Section Fin_sum.
  Context {A B} {HA : Fin A} {HB : Fin B}.
  
  Definition eq_sum' (x y: A + B) := 
    match x,y with
      | inl a, inl b => @equal _ (@eq_fin A HA) a b
      | inr a, inr b =>  @equal _ (@eq_fin B HB) a b
      | _,_ => false
    end. 

  Definition enum_sum (a : list A) (b : list B) := List.app 
    (List.map (fun e => inl  e) a) 
    (List.map (fun e => inr  e) b).
  
  Instance thisequal_type_sum : eqT (A + B) := 
    {| equal := eq_sum'|} . 
  Proof. 
    apply eq_sum_reflect. 
  Defined.   
  Lemma axiom_sum :   forall (x : A + B) , count (equal x) (enum_sum (enum A) (enum B)) = 1.
  Proof.
    intros; unfold enum_sum.
    rewrite count_app.
    case x; intros.
    match goal with
      |- ?x + ?y = 1 => replace y with 0 by now (induction (enum B))
    end.
    rewrite plus_0_r.
    assert (H' := @axiom A HA a). 
    rewrite <- H'. 
    apply count_map. 
    intros b. 
    clear. 
    do 2 case (_eqr); try reflexivity.  
    intros; subst. tauto. intros H; injection H. tauto. 
    match goal with
      |- ?y + ?x = 1 => replace y with 0 by now (induction (enum A))
    end.
    rewrite plus_0_l.
    assert (H' := @axiom B HB b). 
    rewrite <- H'. 
    apply count_map. 
    intros a. 
    clear. 
    do 2  case _eqr; try reflexivity.  
    intros; subst. tauto. intros H; injection H. tauto. 
  Qed.
  
  Global Instance Fin_sum : Fin (A + B) :=
  {| 
    eq_fin := thisequal_type_sum;
    enum := enum_sum (enum A) (enum B);
    axiom := axiom_sum
  |}.
 
  
End Fin_sum. 

Section Fin_sum'.
  Variable A B : Type. 
  Context (X : Fin (A + B)).
  Definition fin_sum_left := 
       List.fold_right
       (fun  (xy : A + B) (l : list A) =>
         match xy with
           | inl x => (x :: l)%list
           | inr _ => l
         end) nil (@enum _ X).
  
  
  Lemma  fin_sum_left_axiom (x : A): 
    count (@equal A (eqT_left A B eq_fin) x) fin_sum_left = 1.
  Proof. 
    unfold fin_sum_left. 
    destruct X as [eqT enum H ]. simpl.
    transitivity (count (equal (inl x)) enum); [ simpl; clear H|apply H]. 
    
    induction enum;[reflexivity|].
    simpl;destruct a. simpl; rewrite IHenum; clear. 

    assert (@equal A (eqT_left A B eqT) x a = equal (inl x ) (inl a)).
    do 2 (case _eqr; intros; subst); congruence.
    rewrite H. reflexivity. 

    rewrite IHenum.
    replace (equal (inl x) (inr b)) with false. reflexivity.
    case _eqr; intros; subst. congruence. congruence. 
  Qed. 

  Instance Fin_sum_left: Fin A
    :=
    {| eq_fin := eqT_left A B (eq_fin); 
       enum := fin_sum_left;
       axiom := fin_sum_left_axiom
      |}.

  Definition fin_sum_right := 
       List.fold_right
       (fun  (xy : A + B) (l : list B) =>
         match xy with
           | inr x => (x :: l)%list
           | inl _ => l
         end) nil (@enum _ X).
  
  
  Lemma  fin_sum_right_axiom (x : B):
    count (@equal B (eqT_right A B eq_fin) x) fin_sum_right = 1.
  Proof. 
    unfold fin_sum_right. 
    destruct X as [eqT enum H ]. simpl.
    transitivity (count (equal (inr x)) enum); [ simpl; clear H|apply H]. 
    
    induction enum;[reflexivity|].
    simpl;destruct a. 
    
    simpl; rewrite IHenum; clear. 
    replace (equal (inr x) (inl a)) with false. reflexivity.
    case _eqr; intros; subst;congruence. 

    simpl. rewrite IHenum. clear. 
    assert (@equal B (eqT_right A B eqT) x b = equal (inr x ) (inr b)).
    do 2 (case _eqr; intros; subst); congruence.
    rewrite H. reflexivity. 
  Qed. 

  Instance Fin_sum_right  : Fin B
    :=
    {| eq_fin := eqT_right A B (eq_fin); 
      enum :=    fin_sum_right;
      axiom := fin_sum_right_axiom
      |}.
End Fin_sum'.


Instance Fin_tag {t} : Fin (tag t):=
  {| 
    eq_fin := eqT_tag;
    enum := cons (tagt t) nil
|}.
Proof. 
  abstract reflexivity. 
Defined. 
