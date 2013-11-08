(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Common Axioms Base Finite. 

(** This file defines a functionnal implementation of the Semantics of
circuits, for loopless ones. We define a simplified model of circuits,
called Loopless, which is identical to traditionnal circuits, except
in the fact that there is no Loop combinator. Compilation is done by a
function of type [circuit -> Maybe.T loopless] *)

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


Module Type T.
  Variable tech : Techno.
  Variable data : Type. 

  Variable sem : forall a b, tech a b -> (a -> data) -> option (b -> data).
End T. 

Module SIM (X : T).
  Import X. 
  Existing Instance tech. 
  Require Import Program. 
 
  Program Fixpoint sim n m (c : circuit n m) : (n -> data) -> option (m -> data) :=
    match c with
      | Atom n m Hfn Hfm x => fun e => sem n m x  e
      | Ser n m p x y => fun e =>
        do e <- sim n m x e;
        sim m p y e
      | Par n m p q x y =>  fun e => 
        do e1 <- sim n p x (fun u => e (inl u) );
        do e2 <- sim m q y (fun u => e (inr u) );
          Maybe.return_ (Data.app e1 e2)
      | Plug n m Hfn Hfm f => 
        fun e => Maybe.return_ (fun X => e (f X))
      | Loop n m l x => fun _ => Maybe.fail 
    end.
End SIM.     


