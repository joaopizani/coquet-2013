(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Axioms Common Base Sumn Finite Reify.
Require Import String. 

Require Import Tagger. 

Module MORE_DOORS. 
  Inductive tech_ :  Techno := 
  | T_NOT  : tech_ unit unit 
  | T_NOR  : tech_ (unit + unit )%type unit 
  | T_NAND : tech_ (unit + unit)%type unit 
  | T_AND  : tech_ (unit + unit)%type unit 
  | T_OR   : tech_ (unit + unit)%type unit 
  | T_XOR  : tech_ (unit + unit)%type unit
    .

  Existing Instance tech_.
  
  Inductive tech_spec_ : @Technology_spec tech_ bool :=
  | TS_NOT : forall ins outs, 
    (outs tt = negb (ins tt))  -> tech_spec_ _ _ T_NOT ins outs
  | TS_NOR : forall ins outs, 
    (outs tt = norb (ins (inl  tt)) (ins (inr  tt))) -> tech_spec_ _ _ T_NOR ins outs
  | TS_NAND : forall ins outs, 
    (outs tt = nandb (ins (inl tt)) (ins (inr  tt))) -> tech_spec_ _ _ T_NAND ins outs
  | TS_AND : forall ins outs, 
    (outs tt = andb (ins (inl tt)) (ins (inr  tt))) -> tech_spec_ _ _ T_AND ins outs 
  | TS_OR : forall ins outs, 
    (outs tt = orb (ins (inl tt)) (ins (inr  tt))) -> tech_spec_ _ _ T_OR ins outs
  | TS_XOR : forall ins outs, 
    (outs tt = xorb (ins (inl tt)) (ins (inr tt))) -> tech_spec_ _ _ T_XOR ins outs
    . 
  
  Existing Instance tech_spec_. 


  Module BLOCK.
    Require Import Program. 
    Definition cst A (f : A -> nat)  := forall  y x, f x = f y . 
    Lemma cst_unit : forall f : unit -> nat, cst _ f. 
    Proof. 
      intros f [] [];    reflexivity. 
    Qed. 
    Lemma ncst_unit2 : ~ (forall f : (unit + unit) -> nat, cst _ f).   
    Proof. 
      intros H. 
      specialize (H ( fun x=> match x with inl  tt => 1 | inr tt  => 2 end ) (inl tt) (inr _ tt)). 
      simpl in H. 
      discriminate.
    Qed. 
    Lemma discr : ~ (@eq Type unit (sum unit unit)).
      intros H. 
      generalize cst_unit. 
      intros H'. 
      rewrite H in H'. 
      apply ncst_unit2. 
      apply H'. 
    Qed.
    
    Lemma inversion_NOT ins outs :  tech_spec_ _ _ T_NOT ins outs ->
    outs tt = negb (ins tt).
    Proof.
      intros H.
      dependent destruction H; auto;   
      exfalso;  apply discr; auto. 
    Qed.  
    Lemma inversion_NOR ins outs :  tech_spec_ _ _ T_NOR ins outs ->
      (outs tt = norb (ins (inl tt)) (ins (inr _ tt))).
    Proof.
      intros H.
      dependent destruction H; auto.  
      exfalso.  apply discr. auto. 
    Qed.
    
    Lemma inversion_NAND ins outs :  tech_spec_ _ _ T_NAND ins outs ->
      (outs tt = nandb (ins (inl tt)) (ins (inr _ tt))).
    Proof.
      intros H.
      dependent destruction H; auto.  
      exfalso.  apply discr. auto. 
    Qed.
    Lemma inversion_AND ins outs :  tech_spec_ _ _ T_AND ins outs ->
      (outs tt = andb (ins (inl tt)) (ins (inr _ tt))).
    Proof.
      intros H.
      dependent destruction H; auto.  
      exfalso.  apply discr. auto. 
    Qed.
    Lemma inversion_OR ins outs :  tech_spec_ _ _ T_OR ins outs ->
      (outs tt = orb (ins (inl tt)) (ins (inr _ tt))).
    Proof.
      intros H.
      dependent destruction H; auto.  
      exfalso.  apply discr. auto. 
    Qed.
    Lemma inversion_XOR ins outs :  tech_spec_ _ _ T_XOR ins outs ->
      (outs tt = xorb (ins (inl tt)) (ins (inr _ tt))).
    Proof.
      intros H.
      dependent destruction H; auto.  
      exfalso.  apply discr. auto. 
    Qed.
  End BLOCK.
  
  Definition NOR a b out : circuit ([:a] + [:b]) [:out]:=
    TAGGER a b out T_NOR.  
  
  Instance NOR_Implement {a b out}: Implement 
    (NOR a b out) 
    (_)%reif 
    _
    (curry norb).
  Proof.
    apply TAGGER_spec.
    intros ins outs H. apply inversion_Atom in H. 
    apply BLOCK.inversion_NOR in H.
    compute. rewrite H.  
    case ins; reflexivity. 
  Qed. 

  Definition NAND a b out : circuit ([:a] + [:b]) [:out]:=
    TAGGER a b out T_NAND.  
  
  Instance NAND_Implement {a b out}: Implement 
    (NAND a b out) 
    (_)%reif 
    _
    (curry nandb).
  Proof.
    apply TAGGER_spec.
    intros ins outs H. apply inversion_Atom in H. 
    apply BLOCK.inversion_NAND in H.
    compute. rewrite H.  
    case ins; reflexivity. 
  Qed. 
End MORE_DOORS. 

