(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
(* Require Import Data EqT Common Finite Reify Base  ZArith String.  *)
(* Require Import Sumn Vector.  *)

Require  Netlist Count Simulation. 
Require  Doors Ripple Muxer.   
Module DATA. 
  Definition data := bool.
End DATA.  
Module DOORS := Doors.DOORS (Doors.ONLY_NOR) <+ Doors.ONLY_NOR <+ DATA.
Module DOORS' := Muxer.MUX(DOORS) <+ DOORS. 
Module ADDER := Ripple.ADD(DOORS') <+ DOORS'.
Require DC. 
Module ADDERS := DC.ADD(ADDER).

Module SIM := Simulation.SIM (ADDER ).
Require Import Reify. 

(** TRUTH TABLE FULL ADDER

Inputs	Outputs
A	B	Cin	Cout	S
0	0	0	0	0
1	0	0	0	1
0	1	0	0	1
1	1	0	1	0
0	0	1	0	1
1	0	1	1	0
0	1	1	1	0
1	1	1	1	1
*)

Require Import EqT. 
Section option. 
  Context `{eqT}.
  Global Instance eqT_option : eqT (option A):=
    {| 
      equal := fun x y => match x,y with 
                           | Some x , Some y => equal x y
                           | None , None => true
                           | _,_ => false
                         end
      |}.
  Proof. 
    abstract 
      (intros [x|] [y|]; try constructor; try discriminate; try reflexivity;
        destruct (_eqr x y);subst; constructor;[ reflexivity | intros H'; injection H'; tauto]). 
  Defined. 
End option. 

(** We can test by simulating the device *)
Check ADDER.FADD. 
Definition test a b cin := 
  let init :=   @uniso _ _ ([b: _] & ([b:_] & [b:_]))%reif (cin, (a, b)) in
  match SIM.sim _ _ (ADDER.FADD "a" "b" "cin" "sum" "cout") init with 
    | None => None
    | Some x =>   
      Some(@iso _ _([b:_] & [b:_])%reif x)
  end.

Eval compute in test true true false. 

Eval compute in List.forallb 
  (
    fun x => match x with 
              | (a,b,cin,cout,s) => equal (Some (s,cout)) (test a b cin)
            end
  )
  (
    (false,false,false,false,false) ::
    (true,false,false,false,true) ::
    (false,true,false,false,true) :: nil
  )%list. 

(**  Same thing with adders *)
Notation I := Reify.Iso_Phi.
Definition test_rca n a b cin  := 
  let init :=   @uniso _ _ ([b:_] & I _ n & I _ n )%reif (cin ,a, b) in
  match SIM.sim _ _ (ADDER.RIPPLE "cin" "a" "b" "cout" "s" n ) init with 
    | None => None
    | Some x =>   
      Some(@iso _ _(I _ n & [b:_])%reif x)
  end.

Eval compute in test_rca 4 (Word.repr 4 3) (Word.repr 4 3) false. 
Eval compute in test_rca 4 (Word.repr 4 8) (Word.repr 4 7) false. 
Time Eval vm_compute in test_rca 4 (Word.repr 4 8) (Word.repr 4 7) true. 


(**  Same thing with adders *)
Require Import String. 
Definition test_dc n a b := 
  let init :=   @uniso _ _ (I _ (Common.pow2 n) & I _ (Common.pow2 n) )%reif (a, b) in
  match SIM.sim _ _ (ADDERS.dv_adder n "x" "y" "s" "t" "g" "p" )%string init with 
    | None => None
    | Some x =>   
      Some(@iso _ _([b:"g"] & [b:"p"] & I _ (Common.pow2 n) & I _ (Common.pow2 n) )%reif x)
  end.

Eval compute in test_dc 2 (Word.repr 4 3) (Word.repr 4 3). 
Eval compute in test_dc 2 (Word.repr 4 8) (Word.repr 4 8). 
Time Eval vm_compute in test_dc 2 (Word.repr 4 8) (Word.repr 4 7). 

(* 
Time Eval vm_compute in test_rca 8 (Word.repr 8  10028) (Word.repr 8 23421) true. 
Time Eval vm_compute in test_rca 9 (Word.repr 9  10028) (Word.repr 9 23421) true. (* 33s *)
Time Eval vm_compute in test_rca 10 (Word.repr 10  10028) (Word.repr 10 23421) true. (* 133s *)
*)
(** We can pretty-print the device  *)
Module DUMPER := Netlist.Netlist(ADDER).

Definition print n := 
  DUMPER.dumper (ADDER.RIPPLE "cin" "a" "b" "cout" "s" n).

Eval vm_compute in  List.length (fst (fst (print 12))). (* 216 NOR doors *)
Eval vm_compute in  List.length (snd (fst (print 10))). (* 1951 internal connection points *)

Require Delay. 

Definition delay_radder n := Delay.compile (ADDER.RIPPLE "cin" "a" "b" "cout" "s" n).
Definition delay_dcadder n := Delay.compile (ADDERS.dv_adder n "x" "y" "s" "t" "g" "p").

Eval compute in (delay_dcadder 2, delay_radder (Common.pow2 2)). 
Eval compute in (delay_dcadder 3, delay_radder (Common.pow2 3)). 
Eval compute in (delay_dcadder 4, delay_radder (Common.pow2 4)). 
(* Eval compute in (delay_dcadder 5, delay_radder (Common.pow2 5)).  *)
