(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Common Base Finite Sumn Vector Reify. 

Module Type T.
  Parameter tech : Techno. 
  Parameter tech_spec_bool : Technology_spec tech bool. 
  Parameter MUX2 : forall a b sel out,
    @circuit tech ([:a] + [:b] + [:sel]) [:out].

  Hypothesis MUX2_Implement : forall a b sel out, 
    @Implement tech bool tech_spec_bool _ _ 
    (MUX2 a b sel out) _ _ 
    ([b: a] & [b: b]  & [b: sel])%reif
    ([b: out])%reif
    (ite).
End T. 

Module MUX (M : T).
  Import M. 
  Existing Instance tech. 
  Existing Instance tech_spec_bool.
  Existing Instance MUX2_Implement. 

  Require Import Vector.
  Definition expand' n (x : bool * vector bool n) := 
    match x with 
      (a,v) => Vector.cons _ a v
    end. 
  
  Instance   Implement_expand {n a}: Implement
    (Plug (@expand [:a] n))
    ([b:a] & [n %- [b:a]])%reif
    ([b:a] & [n %- [b:a]])%reif
    (expand' n).
  Proof. 
    intros ins outs H. 
    apply inversion_Plug in H. 
    rewrite H.
    reflexivity.  
  Qed.      
  
  Definition compact' n (x : vector bool (S n)) := 
    Vector.uncons _ x.
  
  Instance   Implement_compact {n a}: Implement
    (Plug (@compact [:a] n))
    ([b:a] & [n %- [b:a]])%reif
    ([b:a] & [n %- [b:a]])%reif
    (compact' n).
  Proof. 
    intros ins outs H. 
    apply inversion_Plug in H. 
    rewrite H. clear H.
    reflexivity. 
  Qed.      

  Section t.
    Obligation Tactic := idtac. 
    Program Fixpoint MUX n a b sel out : 
      circuit (sumn [:a] n + sumn [:b] n + [:sel]) (sumn [:out] n) :=
      match n with     
        | 0    => Plug (fun x => match x with end)
        | S p  => 
          (Plug (compact _ p) & Plug (compact _ p) & ONE _)
          |> 
            RewireE 
            ([b:a] & [p %- [b: a]] &  ( [b:b] & [p %- [b: b]])  & [b: sel])%reif
            ([b:a] & [b:b] & [b:sel] & 
              ([p %- [b: a]] &  [p %- [b: b]]  & [b: sel]))%reif          
            _
            (fun x => match x return _ with 
                       (a,ap,(b,bp),sel) => 
                       (a,b,sel,(ap,bp,sel))
                     end
            )
            _
          |> (MUX2 a b sel out & MUX p a b sel out) 
          |> Plug (expand _ _)
      end.
    Next Obligation. 
      intros. 
      revert X.
      plug_def. 
    Defined. 
    Next Obligation. 
      intros. plug_auto. 
    Qed. 
    
    Global Instance MUX_Implement {n a b sel out} :
      Implement 
      (MUX n a b sel out)
      ([n %- [b: a]] &  [n %- [b: b]]  & [b: sel])%reif
      ([n %- [b: out]])%reif
      (fun x : vector bool n * vector bool n * bool => match x with 
              | (l,r,b) => if b then l else r
            end  
      ).
    Proof.
      induction n. 
      intros ins outs _.
      unreify_all bool; destruct_all. 
      simpl. case b0; apply (@Vector.nil_eq bool). 


      intros ins outs H; simpl MUX in H. 
      rinvert. realise_all. 
      simpl in ins, outs.   
      unreify_all bool.
      Notation "[ B E : X ]" := (@reify _ B E X).
      simpl. 
      unfold Reify_sum. unfold Reify_Sum. 
      
      unreify_all bool; simpl in *; destruct_all.
      simpl.
      intros_all.
      boolean_eq.
    Qed.    
  End t.
End MUX.  

