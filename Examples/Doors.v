(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Axioms Common Base Sumn Finite Reify.
Require Import String. 
Require Import Tagger Combinators.



Module Type T.
  Parameter tech : Techno. 
  Parameter tech_spec_bool : Technology_spec tech bool. 
  Parameter NOR : forall a b out, @circuit tech ([:a] + [:b]) [:out].
  Hypothesis NOR_Implement : forall a b out, 
    @Implement tech bool tech_spec_bool _ _ 
    (NOR a b out)
    _ _ 
    ([b:a] & [b:b])%reif
    ([b:out])%reif
    (curry norb).
  Parameter label : forall n m (x : tech n m), string.
End T. 

Module DOORS (M : T).
  Import M. 
  Existing Instance tech. 
  Existing Instance tech_spec_bool.
  Existing Instance NOR_Implement. 

  Ltac tac :=  
    rinvert;                    (* destruct the circuit *)
    realise_all;                (* use the hint data-base *)
    unreify_all bool;           (* unreify *)
    destruct_all;               (* destruct the booleans *)
    intros_all; clear; boolean_eq. 

  Ltac tac_discriminate :=  
    rinvert;                    (* destruct the circuit *)
    realise_all;                (* use the hint data-base *)
    unreify_all bool;           (* unreify *)
    destruct_all;               (* destruct the booleans *)
    intros_all; clear; boolean_eq_discriminate. 

  Definition NOT x nx: circuit [:x] [:nx] := Fork2 _  |> (NOR x x nx).
  
  Instance NOT_Implement {x nx} : Implement (NOT x nx) _ _  (negb).
  Proof. 
    intros ins outs H. unfold NOT in H.
    tac. 
  Qed.
  

  Definition OR a b out := NOR a b "m" |> NOT "m" out.
  
  Instance  OR_Implement {a b out}: Implement (OR a b out) _ _ (curry orb).
  Proof. 
    intros ins outs H. unfold OR in H.
    tac. 
  Qed. 

  Definition NAND a b out:=  
    (NOT a "na" & NOT b "nb") |> (OR "na" "nb" out).
  
  Instance NAND_Implement {a  b out}: Implement (NAND a b out) _ _ (curry nandb).
  Proof. 
    unfold NAND; intros ins outs H. 
    (* tac *)
    rinvert.
    realise_all.
    unreify_all bool.
    destruct_all.
    intros_all.
    clear.
    (* boolean_eq *)
    boolean_eq_discriminate.
  Qed.

  Definition AND a b out:= 
    (NOT a "na" & NOT b "nb") |> (NOR "na" "nb" out ).

  Instance AND_Implement {a b out}: Implement (AND a b out) _ _ (curry andb).
  Proof. 
    unfold AND;intros ins outs H; tac_discriminate.
  Qed.

  (* TODO : move RENAME to Base *)
  Definition RENAME a b : circuit [:a] [:b] := Plug (fun x : [:b] => [!a]).
  Instance RENAME_Implement {a b}: Implement (RENAME a b)
    ([b:a])%reif
    ([b:b])%reif
    (id).
  Proof. 
    unfold RENAME. 
    plug_auto. 
  Qed.
  
  Definition BOTH a na ya : circuit [:a] ([:na] + [:ya]) :=
    Fork2 [:a] |> (NOT a na & RENAME a ya).
  
  Instance BOTH_Implement {x nx yx}: Implement (BOTH x nx yx)
    ([b:x])%reif
    ([b:nx] & [b:yx])%reif
    (fun x => (negb x,x)).
  Proof.
    intros ins outs H; unfold BOTH in H; tac_discriminate.
  Qed.

  Program Definition XOR a b out: circuit ([:a] + [:b])  ([:out]):=
    (BOTH a "na" "ya" & BOTH b "nb" "yb")
    |> Rewire _ 
      (fun x : (bool * bool) * (bool * bool)  =>
        let naya := fst x in 
          let nbyb := snd x in 
            ((fst naya, fst nbyb), (snd naya,snd nbyb))
      ) _
      |> (NOR  "na" "nb" "o1" &  NOR "ya" "yb" "o2")
      |>  (* (na x nb) (a x b) *)
          NOR "o1" "o2" out.
  Next Obligation.
    revert H. 
    plug_def. 
  Defined. 
  Next Obligation.
    plug_auto. 
  Defined. 
  
  Instance XOR_Implement {a b out}: Implement (XOR a b out) _ _  (curry xorb). 
  Proof. 
    unfold XOR;   intros ins outs H; tac_discriminate.
  Qed.

  Program Definition MUX2 a b sel out: circuit ([:a] + [:b] + [:sel]) [:out] 
    :=
  Rewire  _ 
  (fun x => match x : bool * bool * bool with (x,y,sel) => (x,sel,(sel,y)) end)
  _
  |> (AND a sel "as" & ((NOT sel "nsel" & ONE _) |>  AND "nsel" b "bs") ) 
  |> OR "as" "bs" out.
  Next Obligation.
   revert H; plug_def. 
 Defined.    
 Next Obligation.
   plug_auto. 
 Qed.

 Instance MUX2_Implement { a b sel out} : 
   Implement (MUX2 a b sel out)
   ([b: a] & [b: b]  & [b: sel])%reif
   ([b: out])%reif
   (ite  ).
 Proof. 
   unfold MUX2;intros ins outs H. tac_discriminate.
 Qed.

 (* TODO : remettre le Fork2 ici *)
 Program Definition HADD a b s c: circuit ( [:a] + [:b]) ([:s] + [:c] ):=
  Rewire _ (fun x : bool * bool => match x with (a,b) => (a,b,(a,b)) end) _
  |> (XOR a b s  & AND a b c).
 Next Obligation. 
   revert H; plug_def. 
 Defined. 
 Next Obligation. 
   plug_auto. 
 Defined. 
  
 Require Import ZArith  Word.
 Instance HADD_Implement {a b s c} : 
   Implement 
   (HADD a b s c)
   _
   _
   (fun (x : bool * bool) => match x with (a,b) =>
                              (xorb a b, andb a b)
                            end
   ).
 Proof. 
   unfold HADD;  intros ins outs H; tac_discriminate.
 Qed.


 Program Definition FADD a b cin sum cout: 
   circuit 
   ([:cin] + ( [:a]  + [:b] )) 
   ([:sum]  + [:cout]):= 
   (ONE [: cin] &  HADD a b "s" "co1")
   |> Rewire _ (fun (x:bool *(bool *bool)) => match x with (a,(b,c)) => ((a,b),c) end) _
   |> (HADD cin "s" sum "co2" & ONE [: "co1"])
     |> Rewire _ (fun (x:(bool *bool) *bool) => match x with ((a,b),c) => (a,(b,c)) end) _
  |> ( ONE ([:sum] ) & OR "co2" "co1" cout ).
 Next Obligation.
   revert H; plug_def.
 Defined. 
 Next Obligation.
   plug_auto. 
 Defined. 
 Next Obligation. 
   revert H; plug_def. 
 Defined. 
 Next Obligation.
   plug_auto. 
 Defined. 

 Require Import Word. 
 
 Instance FADD_Implement {a b cin sum cout} : 
   Implement 
   (FADD a b cin sum cout)
   _  _
   (fun x => 
     match x with (carry,(a,b)) =>
       (xorb a (xorb b carry), 
         ( a && b) || carry && (xorb a b)
       )%bool
     end
   ).
 Proof. 
   (* changed *)
   unfold FADD; intros ins outs H.
   (* tac *)
   rinvert.
   realise_all.
   unreify_all bool.
   destruct_all.
   simpl.
   intros_all.
   clear.

   destruct b0, b1, b2.
   reflexivity.

 Qed.
End DOORS. 

Module ONLY_NOR <: T. 
  
  Instance unit2_Fin: Fin (unit + unit) := Fin_sum.
  
  Inductive tech_ :  Techno := 
  | TNOR : tech_ (unit + unit)%type (unit)
  | TDFF : tech_ unit unit.

  
  Existing Instance tech_.

  Inductive tech_spec_ :@Technology_spec tech_ bool:=
  | TS_NOR : forall ins outs, 
    (outs tt = norb (ins (inl  tt)) (ins (inr tt))) ->
    tech_spec_ _ _ (TNOR ) ins outs. 

  Inductive tech_spec_s :@Technology_spec tech_ (stream bool):=
  | NOR_spec_s : forall ins outs, 
    (forall t, outs tt t = norb (ins (inl  tt) t) (ins (inr tt) t)) ->
    tech_spec_s _ _ TNOR ins outs
  | DFF_spec_s : forall ins outs, 
    ( outs tt = pre false (ins tt)) ->
    tech_spec_s _ _ TDFF ins outs. 
  
  Existing Instance tech_spec_. 
  Existing Instance tech_spec_s. 

  Module BLOCK. 
    
    Definition cst A (f : A -> nat)  := forall  y x, f x = f y . 
    Lemma cst_unit : forall f : unit -> nat, cst _ f. 
    Proof. 
      intros f [] [];    reflexivity. 
    Qed. 
    Lemma ncst_unit2 : ~ (forall f : (unit + unit) -> nat, cst _ f).   
    Proof. 
      intros H. 
      specialize (H ( fun x=> match x with inl  tt => 1 | inr tt  => 2 end ) (inl  tt) (inr  tt)). 
      simpl in H. 
      discriminate.
    Qed. 
    Lemma discr : ~ (@eq Type unit (sum unit unit)).
    Proof. 
      intros H. 
      generalize cst_unit. 
      intros H'. 
      rewrite H in H'. 
      apply ncst_unit2. 
      apply H'. 
    Qed.

    Require Import Program. 
    Lemma inversion_NOR : forall ins outs, tech_spec_ _ _ (TNOR ) ins outs -> 
      (outs tt = norb (ins (inl _ tt)) (ins (inr _ tt))).
    Proof.
      intros. 
      dependent destruction H. 
      auto. 
    Qed.

    Lemma inversion_NOR_stream : forall ins outs, tech_spec_s _ _ TNOR ins outs -> 
      (forall t, outs tt t = norb (ins (inl _ tt) t) (ins (inr _ tt) t)).
    Proof.
      intros. 
      dependent destruction H. 
      auto. 
      apply discr in x0. tauto. 
    Qed.

    Lemma inversion_DFF_stream : forall ins outs, tech_spec_s _ _ TDFF ins outs -> 
      ( outs tt = pre false (ins tt)).
    Proof.
      intros. 
      dependent destruction H. 
      symmetry in x0. apply discr in x0. tauto. 
      auto. 
    Qed.
  End BLOCK.
 
  Lemma inversion_NOR : forall ins outs, tech_spec_ _ _ TNOR ins outs -> 
    (outs tt = norb (ins (inl _ tt)) (ins (inr _ tt))). 
  Proof. apply  BLOCK.inversion_NOR. Qed.
  
  Definition NOR a b out : circuit ([:a] + [:b]) [:out]:=
    TAGGER a b out TNOR.  

  Definition DFF a out : circuit ([:a]) [:out]:=
    Plug (fun _ => [!a]) |> Atom TDFF |> Plug (fun _ => tt).  

  Instance NOR_Implement {a b out}: Implement 
    (NOR a b out) 
    (_)%reif 
    _
    (curry norb).
  Proof.
    apply TAGGER_spec.  
    intros ins outs H. apply inversion_Atom in H. 
    apply inversion_NOR in H.
    compute. rewrite H.  
    do 2 case ins; reflexivity. 
  Qed. 

  Instance NOR_Implement_stream {a b out}: Implement 
    (NOR a b out) 
    (Iso_compose (Iso_tag _ _ & Iso_tag _ _)  (Iso_prod_stream _ _) )%reif 
    (_)
    (Stream.map (curry norb)).
  Proof.
    intros ins outs H. 
    Notation "[ X  : B ]" := (@reify _ B _ X).
    
    apply (TAGGER_spec _ (fun x => 
      let y :=@iso _ _ (Iso_prod_stream _ _ ) x in 
        Stream.map (curry norb) y
    )) in H. 
    
    etransitivity; etransitivity.  2: apply H.  reflexivity. 
    reflexivity. 
    simpl. 
    reflexivity.
    clear. intros ins outs H. 
    apply inversion_Atom in H. 
    apply functional_extensionality. 
    intros t. 
    assert (H' := @BLOCK.inversion_NOR_stream _ _ H t). clear H.
    compute. rewrite H'. do 2 case ins; reflexivity.   
  Qed. 

  Instance DFF_Implement_stream {a  out}: Implement 
    (DFF a out) 
    ((Iso_tag _ _ ) )%reif 
    (_)
    (pre false ).
  Proof.
    intros ins outs H. 
    unfold DFF in H. 
    rinvert. 
    apply inversion_Atom in Hk1.
    apply BLOCK.inversion_DFF_stream in Hk1. 
    apply inversion_Plug in Hk. 
    apply inversion_Plug in Hk0. 
    rewrite Hk0. apply functional_extensionality.  intros t. 
    compute. rewrite Hk1. rewrite Hk. clear. compute. reflexivity. 
  Qed.     

  Definition tech := tech_. 
  Definition tech_spec_bool := tech_spec_. 

  Definition sem {a b } (x: tech a b) :  ( a -> bool) -> option (b -> bool) :=
    match x with
      | TNOR => fun e => Some (fun _ => norb (e (inl tt)) (e (inr tt)))
      | TDFF => fun e => None
    end.
  
  Definition label n m (x : tech n m) := 
    match x with 
      | TNOR => ("nor")%string
      | TDFF => ("dff")%string
    end.
End ONLY_NOR. 
