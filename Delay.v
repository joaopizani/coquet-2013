(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Base. 
Require Import String Finite EqT. 


Module Maybe.
  Definition T (a : Type) := option a. 
  Definition return_ {A : Type} (x : A) : T A := Some x.
  Definition fail {A : Type } : T A := None.
  Definition bind {A B : Type} (a : T A) (f : A -> T B) : T B :=
    match a with
      | Some x => f x
      | None => None
    end.


  Lemma bind_Some {A B} (a : T A) (y : B) (f : A -> T B) :
    bind a f = Some y -> 
    exists x,( a = Some x /\ f x = Some y ). 
  Proof.
    intros. 
    destruct a.  exists a. intuition. 
    simpl in H. discriminate. 
  Qed.
  
End Maybe. 

Notation "x >> f" := (Maybe.bind x f) (at level 60).
Notation "'do' a <- e ; c" := (e >> (fun a => c)) (at level 60, right associativity).


Section t.
  Context {tech : Techno}. 
  
  Require Import JMeq. 
  Fixpoint compile {n} {m} (x : circuit n m) :=
    match x with
      | Atom n m fn fm x => Maybe.return_ 1
      | Ser n' m' p' x y => 
        do x <- compile  x;  
        do y <- compile y ; Maybe.return_ (x + y)
      | Par n m p q x y => 
        do x <- compile  x;  
          do y <- compile y ; Maybe.return_ (Max.max x y)
      | Plug n m fn fm f => Maybe.return_ 0
      | Loop n m l x => 
        Maybe.fail
    end.
      
End t. 

