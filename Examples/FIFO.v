(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Data EqT Common Finite Reify Base  ZArith String. 
Require Import Sumn Vector. 

Module Type T.
  Parameter tech : Techno. 
  Parameter tech_spec : Technology_spec tech (stream bool). 


  Parameter DFF: forall a out, @circuit tech [:a]  [:out].
  
  Hypothesis  DFF_Implement : forall a  out, 
    @Implement tech (stream bool) tech_spec _ _
    (DFF a out) _ _
    _
    _
    (fun x => pre false x ).
End T. 
  
Module FIFO (X : T).
  Import X. 
  Require Import Combinators. 
  Existing Instance tech. 
  Existing Instance tech_spec. 
  Definition FIFO x (width length : nat) :=
    COMPOSEN (map (DFF x x) width) length.

  Require Import Bool_nat. 
  Definition default width := Vector.vector_repeat width false.
  Definition fifo width length (v : stream (vector bool width)) : stream (vector bool width) :=
    fun t => if lt_ge_dec t length then default width else v ( t - length).
  
  Definition I x n : Iso (sumn [:x] n -> stream bool) (stream (vector bool n)) :=
    Iso_compose (Iso_sumn _ (Iso_tag _ x) n)(Iso_vector_stream _ n ).
  
  Lemma FIFO_Spec x width length : 
    Implement (FIFO x width length)
    (I x width) (I x width)
    (fifo width length).
  Proof. 
    unfold FIFO. intros ins outs H. 
    
    eapply (COMPOSEN_Spec _ _ (I x width) (pre (default (width)))) in H. rewrite H. 
    unfold fifo. 
    clear H. 
    unreify_all (stream bool). 
    
    generalize ins0 as ins. clear. 
    induction length. 
    simpl.  unfold id. Require Import Axioms. 
    Require Import Arith. intros.
    apply functional_extensionality.
    intros. f_equal.  rewrite <- minus_n_O. reflexivity. 
    simpl. 
    intros. rewrite IHlength. apply functional_extensionality.
    intros. unfold pre. 
    repeat case lt_ge_dec;  intros; try reflexivity ; try (exfalso; omega). 
    assert (x = length). omega.  subst. rewrite minus_diag. reflexivity. 
    assert (exists p, x - length = S p). exists (x - S length). omega.
    destruct H.  rewrite H. replace (x - S length) with x0 by omega.
    reflexivity. 
    clear. 
  
    intros ins outs H. 
    eapply (map_Implement ) in H. 
    2: apply DFF_Implement.
    Notation "[ B : X ]" := (@reify _ B _ X).
    revert H. 
    cast outs ((Iso_vector_stream bool width)).
    2:reflexivity.   
    unreify_all (stream bool).
    cast ins ((Iso_vector_stream bool width)). 2: reflexivity. 
    unreify_all (stream bool).
    intros.
    rewrite H. clear.
    
    
    apply functional_extensionality. intros x. simpl.
    
    induction width. compute. destruct x; reflexivity. 
    simpl. simpl in *. destruct ins0. 
    rewrite IHwidth.
    unfold pre. 
    simpl. unfold default. simpl. destruct x.   f_equal. reflexivity. 
  Qed.
End FIFO.