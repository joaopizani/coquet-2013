(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Base. 
Require Import String Finite EqT. 

(** We define how to pickle from finite types  *)

Section pick. 
  Context `{Fin}.
  Instance eqA : eqT A := eq_fin. 

  Fixpoint find (e : A) i l {struct l}:= 
    match l with 
      | nil => None
      | cons t q => if equal e t then Some i else find e (i+1) q
    end. 

  Lemma find_Some : forall e, exists x, find e 0 (enum A) = Some x.
  Proof.
    intros e. 
    assert (H' := axiom e).
    induction enum. simpl in H'.  discriminate. 
    simpl in *.
    unfold eqA. 
    destruct (@equal A (@eq_fin A H)e a). exists 0.
    reflexivity.
    destruct IHl.
    auto.
    exists (x+1).

    Lemma find_gen : forall e l i j x, 
      find e i l = Some x -> 
      find e (i+j) l = Some (x +j).
      intros e. induction l. simpl. intros; discriminate.
      intros. simpl.
      simpl in H0. 
      unfold eqA in *. 
      destruct (@equal A (@eq_fin A H)e a). 
      congruence.
      apply (IHl _ j)in H0.  clear IHl. rewrite <- H0. 
      f_equal. Require Import Arith. ring. 
    Qed.
    change (1) with (0+1). 
    apply find_gen. auto. 
  Qed.

  Program Definition pickle : A -> nat := fun x => 
    match find x 0 (enum A)  with 
      | None => _
      | Some p => p
    end. 
  Next Obligation.
    abstract 
      (exfalso; destruct (find_Some x); congruence). 
  Defined.
End pick.

Class Pick A (F : Fin A) :=
  pick : A -> nat.

(* We do not prove this property yet *)
Class GoodPick `{Pick} :=
  good_pick : forall x, pick x = pickle x.

Instance DefaultPick A (F : Fin A) : Pick A F | 100 := pickle .

Section picks. 
  Global Instance Pick_zero : Pick _ Fin_zero := fun x => 0. 
  
  Context A FA {PA : Pick A FA}.
  Context B FB {PB : Pick B FB}.

  Global Instance Pick_sum : Pick _ (@Fin_sum A B FA FB) := 
    fun x => 
      match x with 
        inl e => PA e 
        | inr e => List.length (enum A) + PB e
      end.
End picks.

Module State.
  Section t. 
    Context {sigma : Type}.
    Definition T (a: Type) := sigma -> a * sigma.
    
    Definition return_ {a : Type} (x : a) : T a := fun s => (x,s).
    Definition bind {a b: Type} ( m : T a) (f : a -> T b ):= 
      fun r => 
        let (x,s) := m r in (f x) s.
    Definition get : T sigma := fun s => (s,s).
    Definition put x : T unit := fun s => (tt, x).
    Definition modify (f : sigma -> sigma) : T unit  :=
      fun s => (tt, f s).
  End t.
End State. 

Notation "x >> f" := (State.bind x f) (at level 60).
Notation "'do' a <- e ; c" := (e >> (fun a => c)) (at level 60, right associativity).

 
Require Import NArith. 

Module Type T.
  Parameter tech : Techno. 
  Parameter label : forall n m (x : tech n m), string.
End T.
Module Netlist (X : T).
  Import X. 
  Existing Instance tech. 

  Definition fresh_map a {fa : Fin a}: @State.T N (a -> N) := fun sigma =>
    (   
      let s := N_of_nat #|a| in 
      let x := 
        fun e => 
          let e' := pick e in (N_of_nat e' + sigma)%N
      in
      (x, sigma + s)%N
    ).  
  
  Record instance := mk_instance
    {
      _door : string;
      wire_in : list N;
      wire_out : list N
    }.
  
  
  Definition build_instance {n m} (fn : Fin n) (fm : Fin m) 
    (x : tech n m  )
    (pick_in : n -> N) 
    (pick_out : m -> N): instance :=
    mk_instance 
    ("nor")%string 
    (List.map pick_in (enum n)) 
    (List.map pick_out (enum m)). 
  
  Definition build_plug {n m}
    (fn : Fin n) (fm : Fin m) 
    (x : m -> n )
    (pick_in : n -> N) 
    (pick_out : m -> N): list (N * N):=
    List.map (fun a => (pick_in (x a), pick_out a)) (enum m).

  Definition dump := (list instance * list (N * N))%type.
    
  Definition app (x : dump) (y : dump) :=
    let (lx,ufx) := x in 
    let (ly,ufy) := y in 
      (List.app lx ly, List.app ufx ufy).

  Require Import JMeq. 
  Fixpoint compile {n} {m} (fn : Fin n) (fm : Fin m) (x : circuit n m) 
    : (n -> N) -> (m -> N) -> State.T (dump) :=
    match x with
      | Atom n m fn fm x => fun ins out => 
        let r := build_instance fn fm x ins out 
          in State.return_  ( r :: List.nil , List.nil)%list
      | Ser n' m' p' x y => fun ins out =>
        do mid <- @fresh_map  m' (circuit_fin_r (x:=x));
        do r1 <- compile (circuit_fin_l (x := x)) (circuit_fin_r (x := x)) x ins mid;
        do r2 <- compile (circuit_fin_l (x := y)) (circuit_fin_r (x := y)) y mid out;
          State.return_ (app r1 r2)            
      | Par n m p q x y => fun ins out => 
        let i1 := Data.select_left ins in 
        let i2 := Data.select_right ins in 
        let o1 := Data.select_left  out in 
        let o2 := Data.select_right out in 
          do r1 <- compile (circuit_fin_l (x := x)) (circuit_fin_r (x := x)) x i1 o1;
          do r2 <- compile (circuit_fin_l (x := y)) (circuit_fin_r (x := y)) y i2 o2;
            State.return_ (app r1 r2)          
      | Plug n m fn fm f => 
        fun ins out =>  
          let r := build_plug fn fm f ins out in 
            State.return_ (List.nil , r)
      | Loop n m l x => 
        fun ins outs => 
          do retro <- @fresh_map l (Fin_sum_right _ _ (circuit_fin_l (x:=x)) ); 
            compile  (circuit_fin_l (x := x)) (circuit_fin_r (x := x)) x (Data.app ins retro) (Data.app outs retro)
    end.

  Definition dumper {n} {m} (x : circuit n m) :=
    let fn := (circuit_fin_l (x:=x)) in
    let fm := (circuit_fin_r (x:=x)) in
    (do i <- @fresh_map n fn ;
     do o <- @fresh_map m fm ;
      compile fn fm x i o) 0%N.
      
End Netlist. 

(*Require Import Adder AnnDoors. 
Module t1. 
  Definition test := (@XOR "a" "b" "out" ).  
  Eval compute in dumper (test ).
End t1. 

Module t2. 
  
  Definition test n := (@ripple_carry_adder _ (@FADD) "a" "b" "sum" "carry"n)%string.
  Time Eval compute in dumper (test 1).
End t2. *)
