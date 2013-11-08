(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

(** Generalized n-ary disjoint sums  *)

Require Import Common EqT Finite. 
Require List. 

Section Sumn. 
  Variable A : Type. 

  Fixpoint sumn (n : nat) : Type :=
    match n with 
      | 0 => zero
      | S n => (A + sumn n  )%type
    end.

  
  Definition expand  n  (x : sumn  (S n) ) : (A + sumn   n)%type := id x.
  Definition compact n (x : A + sumn  n) : sumn (S n) := id x. 

  Fixpoint  sumn_add x y {struct x}:
    sumn x + sumn  y ->  sumn  (x+y) :=
    match x with 
      | 0 => fun e => match e with inl e => match e with end | inr e => e end
      | S p => fun e => 
        match e with 
          |inl asp => 
            let asp := expand p asp in
              match asp with
                | inl el => inl  el
                | inr t => inr  (sumn_add _ _ (inl t))
              end
          |inr ay => inr  (sumn_add _ _ (inr  ay))
      end         
  end. 

  
  Fixpoint sumn_add' x y {struct x}:   sumn (x+y) -> sumn  x + sumn  y :=
    match x with 
      | 0 => fun e => inr  e
      | S p => fun e => 
        match e with
          | inl e => inl (inl  e)
          | inr t => 
            let t' := sumn_add' _ _ t in 
              match t' with
                | inl t0 => inl  (inr t0)
                | inr t0 => inr t0
              end
        end
    end. 

 
  Definition sumn_1 : sumn  1 -> A := fun e => 
    match e with 
      | inl e => e
      | inr e => match e with end
    end.

 
End Sumn. 


Notation " ! " := (zero_rect _ _).

Section ops. 
  Variable A B : Type. 
  Definition sumn_zip  n : sumn A n + sumn B n -> sumn (A+B) n.
  Proof. 
    induction n; firstorder. 
  Defined.
  
  Definition sumn_unzip n : sumn (A + B) n -> sumn A n + sumn B n. 
  Proof.
    induction n; firstorder. 
  Defined.
  
  Definition sumn_forget_left n: sumn A n -> sumn (A + B) n . 
  Proof. 
    induction n. 
    intros []. 
    intros X; apply compact; apply expand in X; destruct X as [X |X]. 
    repeat left; apply X. 
    right. apply (IHn X).
  Defined. 
  
  Definition sumn_forget_right n : sumn B n -> sumn (A + B) n . 
  Proof. 
    induction n. 
    intros []. 
    intros X; apply compact; apply expand in X; destruct X as [X |X]. 
    auto. 
    auto. 
  Defined. 

  Fixpoint sumn_map n (f : A -> B): sumn A n -> sumn B n  :=
    match n with 
      | 0 => fun e => match e with end
      | S p => fun e => match expand A p e with 
                     | inl e => inl (f e)
                     | inr e => inr (sumn_map p f e)
                      end
    end.
  
  Fixpoint sumn_repeat n : sumn A n -> A := 
    match n with 
      | 0 => fun e => match e with end
      | S p => fun e => match expand A p e with 
                        | inl e => e
                        | inr e => sumn_repeat p e 
                      end
    end.
                                             
  
End ops. 

Section Eq. 
  Context `{eqT}. 
  
  Fixpoint eqb_sumn n : sumn A n -> sumn A n -> bool := (* bug avec Program : insere des obligations *)
    match n with 
      | 0 => fun x _ => match x with end 
      | S p => fun x y => match x, y with
                          | inl a, inl b => equal a b
                          | inr a, inr b => eqb_sumn p a b
                          | _ , _  => false
                        end
    end.
  
  Lemma eqb_sumn_reflect n : 
      forall x y : sumn A n, Bool.reflect (x = y) (eqb_sumn n x y).
  Proof. 
        induction n.
    simpl; intros; tauto.
    simpl sumn. 
    intros [x|x] [y|y];
    simpl eqb_sumn. 
    case (_eqr); intros Hxy; constructor. 
    subst. reflexivity. 
    intros H'.  injection H'. clear H'; intros H'; subst; tauto. 
  
    constructor. discriminate. 
    constructor. discriminate. 
    specialize (IHn x y).
    revert IHn. 
    case (eqb_sumn n x y); intros H'; inversion H'.  subst. constructor. reflexivity. 

    constructor. 
    intros H''.  injection H''. clear H''; intros H''; subst; tauto. 
  Qed.
  Global Instance eqT_sumn {n}: eqT (sumn A n) :=
    {| equal := eqb_sumn n|}.
  Proof. 
    apply eqb_sumn_reflect.
  Defined.

End Eq. 

Fixpoint flatten A (l : list (list A)) : list A :=
    match l with 
      | nil => nil
      | cons t q => List.app t (flatten A q)
    end.
  
Section Fin_sumn.
  Context {A : Type} {F : Fin A}.
 
  Fixpoint enum_sumn n : list (sumn A n) :=
    match n with 
      | 0 => [ :: ]%list
      | S p => enum_sum (enum A) (enum_sumn p)
    end. 
  Instance local {n}: eqT (sumn A n) :=
    let f := F in match f with
                    | {| eq_fin := eq_fin |} => eqT_sumn
                  end.

  Lemma fin_sumn_axiom n:  forall x : sumn A n, count (equal x) (enum_sumn n) = 1.
  Proof. 
        induction n. simpl; tauto. 
    simpl.
    intros [x|x];
    unfold enum_sum;
    rewrite count_app.
    assert (H' := @axiom A F x). 
    rewrite <- H'. 
    match goal with 
      |- ?x + ?y = _ => replace y with 0
    end. 
    Require Import Arith. 
    rewrite plus_0_r. 
    apply count_map. 
    intros a.
    do 2 case _eqr; try  reflexivity; intros; subst; try tauto. 
    injection e. tauto. 

    symmetry. 
    clear. induction (enum_sumn n); simpl; try reflexivity.   
    case _eqr.     intros; discriminate. intros. auto. 

    match goal with 
      |- ?y + ?x = _ => replace y with 0
    end. 
    Require Import Arith. 
    rewrite plus_0_l. 
    rewrite <- (IHn x). 
    apply count_map. 
    intros a.
    do 2 case _eqr; try  reflexivity; intros; subst; try tauto. 
    injection e. tauto. 

    symmetry. 
    clear. induction (enum A); simpl; try reflexivity.   
    case _eqr.     intros; discriminate. intros. auto.  
  Qed.
  Global Instance Fin_sumn {n} : Fin (sumn A n) :=
    {| 
      eq_fin := local;
      enum := enum_sumn n
    |}.
  Proof. 
    apply fin_sumn_axiom.
  Defined.
End Fin_sumn. 
