(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

(** Some definitions we re-use through the development *)

Require Import String. 
Require Import Axioms. 

(** Tagged units, to sort the mess of the wires *)
Inductive tag (t : string) : Type :=
  tagt : tag t.  

Notation "[: x ]" := (tag x).
Notation "[! x ]" := (tagt x).
Notation "[!!]" := (tagt _).

(** The type with zero elements, for the wires  *)
Inductive zero : Type := . 

(** Some operations on sum, that can be used to build plugs  *)
Implicit Arguments inl [A B].
Implicit Arguments inr [A B].
Section sum. 
  Context {A B C : Type}.
  Definition sum_assoc : A+ (B + C) -> (A+B) + C := 
    fun x => match x with 
              | inl e => inl  (inl  e)
              | inr (inl e) => inl (inr  e)
              | inr (inr e) => inr e
            end. 
  Definition sum_assoc' : A + B + C -> A + (B + C) := fun x => 
    match x with
      | inl (inl e) => inl e
      | inl (inr e) => inr (inl e)
      | inr e => inr (inr e)
    end.

  Definition sum_comm : A + B -> B + A :=
    fun x => match x with 
              | inl e => inr e
              | inr e => inl e
            end.

  Definition sum_compat_right : (A + B) -> (B -> C) ->  (A + C) := fun x => fun f => 
    match x with 
      | inl a => inl a 
      | inr b => inr (f b)
    end. 
  
  Definition sum_compat_left : (B + A) -> (B -> C) ->  (C + A) := fun x => fun f => 
    match x with 
      | inl b => inl (f b) 
      | inr a => inr a
    end.   
End sum.

(**  Streams *)
Definition stream A := nat -> A. 

Module Stream.
  Section ops. 
    Context { A B : Type}. 
    Variable f : A -> B. 
    Definition map : stream A -> stream B := fun s t => 
      f (s t).

    Definition zip : stream A -> stream B -> stream (A*B) :=
      fun sA sB t => 
        (sA t, sB t).
    
    Definition unzip : stream (A*B) -> stream (A) * stream B :=
      fun s => 
        (fun t => fst (s t), fun t => snd (s t)).
    Lemma unzip_zip : forall x y, unzip (zip x y) = (x, y).
    Proof. 
      intros; compute. 
      reflexivity. 
    Qed.
  End ops. 
End Stream. 
    
(** curry/uncurry *)
Definition uncurry {A B C: Type} (f : A*B -> C) : A -> B -> C :=
  fun x => fun y => f (x,y).

Definition curry {A B C : Type} (f : A -> B -> C): A*B -> C :=
  fun x => f (fst x) (snd x).

Notation "[$ f ]" := (curry f). 

(** Some boolean functions *)
Section booleans. 
  Require Import Bool. 
  Definition norb x y := negb (orb x y).
  Definition nandb x y := negb (andb x y).


  Definition ite (x : bool * bool * bool):= 
    match x with 
      (l,r,b) => if b then l else r
    end. 

End booleans. 

Definition pre {A} (default : A): stream A -> stream A := fun f t =>
  match t with 
    | 0 => default
    | S p => f p
  end.

Ltac boolean_eq :=
  repeat match goal with 
           | x : bool |- _ => destruct x
         end;
  reflexivity.



Fixpoint pow2 k := match k with O => 1 | S p => pow2 p + pow2 p end.

Notation "[2^ n ]":= (pow2 n).

Definition time {A Data}  (f : A -> stream Data) (n : nat) : A -> Data :=
  fun x => f x n.
