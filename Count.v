(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Base. 
Require Import String Finite EqT. 

Section t.
  Context {tech : Techno}. 
  
  Require Import JMeq. 
  Fixpoint compile {n} {m} (x : circuit n m) 
    : nat :=
    match x with
      | Atom n m fn fm x => 1
      | Ser n' m' p' x y => compile  x + compile y
      | Par n m p q x y => compile  x + compile y
      | Plug n m fn fm f => 0
      | Loop n m l x => 
        compile  x
    end.
      
End t. 

