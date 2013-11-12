(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Common Base Finite Sumn Vector Reify. 

Module Type T.
  Parameter tech : Techno. 
  Parameter tech_spec_stream : Technology_spec tech (stream bool). 

  
  Parameter MUX2 : forall a b sel out, @circuit tech ([:a] + [:b] + [:sel]) [:out].
  Parameter DFF : forall a out, @circuit tech [:a] [:out].
  
  Remark iso1 a b sel : Iso ([:a] + [:b] + [:sel] -> (stream bool)) (stream (bool * bool * bool)).
  Proof. 
    eapply Iso_compose. 
    2:apply Iso_prod_stream. 
    apply Iso_sum. 2: apply Iso_tag. 
    eapply Iso_compose. 
    2:apply Iso_prod_stream. 
    apply Iso_sum; apply Iso_tag. 
  Defined. 
  Hypothesis (Implement_MUX2 : forall a b sel out, @Implement tech (stream bool) tech_spec_stream _ _ (MUX2 a b sel out) _ _
    (iso1 a  b sel)
    (Iso_tag _ _ )
    (Stream.map ite)). 

  Hypothesis (Implement_DFF: forall a out, @Implement tech (stream bool) tech_spec_stream _ _ (DFF a out) _ _
    (Iso_tag _ _ )
    (Iso_tag _ _ )
    (pre false)). 

End T. 

Module Register1bit (X : T).
  Import X. 

  Existing Instance tech. 
  Existing Instance tech_spec_stream. 
  
  
  Require Import String. 
  Open Scope string_scope. 
  
  Variable load a out : string. 
  Program Definition register : circuit ([:load] + [:a]) [:out]:=
    @Loop _ ([:load] + [:a]) [:out]  [:out] 
    (RewireE (iso1 load a out) (iso1 a out load) _ 
      (fun s => fun t => match s t return _ with (l,a,o) => (a,o,l) end)
      _ 
      |> MUX2 a out load "in_dff"%string 
      |> DFF "in_dff" out 
      |> 
      Rewire (fun x => match x with inl e => e | inr e => e end) (fun x => (x,x)) _ ).
  Next Obligation. 
    revert H. plug_def.   
  Defined. 
  Next Obligation. 
    plug_auto. 
  Qed. 
  Next Obligation. 
    plug_auto. 
  Qed. 

  Definition Iso2 a b : Iso ([:a] + [:b] -> stream bool) (stream (bool * bool)).
  Proof. 
    eapply Iso_compose. 2: apply Iso_prod_stream. 
    apply Iso_sum; apply Iso_tag. 
  Defined. 
  Instance register_DataAbstraction :
    Realise register 
    (Iso2 load a )
    (Iso_tag _ out)
    (fun (ins : stream (bool * bool)) (outs : stream bool) => 
      outs = pre false (fun t => 
        let (load, inputs) := ins t in 
        if  load then inputs else outs t
      )).
  Proof. 
    intros ins outs H; unfold register in H. 
    apply inversion_Loop in H; destruct H as [retro H].
    rinvert. 
    apply Implement_MUX2 in Hk2. 
    apply Implement_DFF in Hk1.
    realise_all. 
    unreify_all (stream bool).
    Notation "[ X : B (via  R ) ]" := (@reify _  B R X) : view_scop.
    unfold Reify_tag in *. 
    unreify_all (stream bool). 
    
    match goal with 
      |- context [@reify _ _ (Reify_sum _ ?R ?R') (Data.app ?x ?y)] =>
        replace (@reify _ _ ((Reify_sum _ R R')) (Data.app x y)) with 
          (@reify _ _ R x, @reify _ _ R' y)
    end. 
    2: symmetry; apply reify_app. 
    unreify_all (stream bool).
    intros_all. intros.
    Require Import Axioms. apply functional_extensionality. intros. 
    rewrite H0; clear H0 outs0. 
    rewrite <- H. rewrite <- H in Hk1. clear H mid0. 
    rewrite Hk2 in Hk1; clear Hk2 mid1. 
    rewrite Hk in Hk1.  clear Hk mid2. 
    assert (H := equal_f Hk1 x). clear Hk1.
    unfold Stream.map in H. unfold pre in *.
    compute. compute in H.  apply H. 
  Qed.

End Register1bit. 

