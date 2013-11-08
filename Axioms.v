(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

(** This file collect the axioms used through our development  *)

Require Export FunctionalExtensionality. 
Require Export ProofIrrelevance.


(* Axiom functional_extensionality_dep : forall {A} {B : A -> Type},  *)
(*   forall (f g : forall x : A, B x),  *)
(*   (forall x, f x = g x) -> f = g. *)


(* Axiom proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2  *)