(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Axioms Common Base Sumn Finite Reify.
Require Import String. 


Section t. 
  Context {tech : Techno} {Data : Type}. 
  Context {tech_spec : Technology_spec tech Data}. 

  Definition TAGGER a b out (c : tech (unit + unit)%type unit ) :=
    Plug (fun x => match x with  
                    | inl e => inl [!a]
                    | inr e => inr [!b]
                  end ) 
    |> Atom c 
    |> Plug (fun (x : [:out]) => tt).
  
  Lemma TAGGER_spec  (c : tech (unit+unit)%type unit) f :
    Implement 
    (Atom c)
    (Iso_unit Data & Iso_unit Data)%reif
    (Iso_unit Data)%reif
    (f) ->
    (forall a b out,
      Implement 
      (TAGGER a b out c)
      (Iso_tag _ _  & Iso_tag _ _ )%reif (Iso_tag _ _)%reif
      f)
      .
  Proof. 
    intros. unfold TAGGER.  intros ins outs H'.  rinvert. apply H in Hk1. 
    apply inversion_Plug in Hk. 
    apply inversion_Plug in Hk0. clear H. 
    subst.
    compute in Hk1. compute. rewrite Hk1. clear Hk1. 
    reflexivity. 
  Qed.  
End t. 
