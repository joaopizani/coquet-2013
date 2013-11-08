(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Data EqT Common Finite Reify Base  ZArith String. 
Require Import Sumn Vector. 
  
Section void. 
  Context {tech : Techno}. 
  Context (tech_spec : Technology_spec tech bool).

  Definition swap a b: circuit ([:a] + [:b]) ([:b] + [:a]) :=
    Plug (sum_comm).

  Definition Id a :=
    Loop (swap a _).
  
  Lemma Implement_id a ins outs: Semantics (Id a) ins outs -> outs = ins. 
  Proof. 
    intros H. unfold Id in H.  
    apply inversion_Loop in H. 
    destruct H. unfold swap in H. apply inversion_Plug in H. 
    Require Import Axioms. 
    apply functional_extensionality. 
    intros e.
    apply Data.app_projections in H. 
    destruct H as [Hx Hy].
    rewrite Hx. 
    rewrite Hy. 
    reflexivity. 
Qed.
End void.

Section not. 
  Context {tech : Techno}. 
  Context (tech_spec : Technology_spec tech bool).

  Variable NOT : forall a out, circuit [:a] [:out].
  Hypothesis H : forall a out, Implement (NOT a out) ([b: _])%reif _ (fun x =>  (negb x)).

  
  Program Definition Unstable a : circuit zero [:a]:=
    @Loop _ _ _ [:a] ( Plug _ |>  NOT a a |> Plug _).
  Next Obligation. 
    revert H0. plug_def. 
  Defined.     
  Next Obligation. 
    revert H0. plug_def. 
  Defined.     
  
  
  Lemma unstable a : forall ins outs, ~ Semantics (Unstable a) ins outs. 
  Proof. 
    intros ins outs H'. 
    unfold Unstable in H'.  
    apply inversion_Loop in H'. 
    destruct H'.  rinvert. 
    apply inversion_Plug in Hk.     apply inversion_Plug in Hk0. 
    apply H in Hk1. clear H.
    rewrite Hk in Hk1. clear Hk. clear mid0. unfold lift, Unstable_obligation_1 in Hk1.  
    Lemma iso_move : forall A B (I : Iso A B) (H : Iso_Props I) (x : A) y, 
      @iso A B I x = y <-> x = @uniso A B I y. 
      clear. 
      split; intros. 
      rewrite <- H0. rewrite uniso_iso. reflexivity. 
      rewrite H0. rewrite iso_uniso. reflexivity. 
    Qed.
    unfold reify in Hk1. 
    rewrite iso_move in Hk1. 
    rewrite Hk1 in Hk0. 
    clear Hk1. clear mid. 
    compute in Hk0. 
    assert (H := equal_f Hk0 (inr [!!])).  simpl in H.  clear - H. 
    destruct (x [!!]); discriminate. 
    
    unfold reify_. apply Iso_Props_tag. 
  Qed.
End not.


(** The so-called hamlet circuit, in the boolean model *)
Module hamlet. 
  Section t. 
    Context {tech : Techno}. 
    Context (tech_spec : Technology_spec tech bool).
    
    Variable ORNOT : forall a b out, circuit ([:a] + [:b]) [:out].
    Hypothesis realise_ornot : forall a b out, Implement (ORNOT a b out) ([b: _] & [b:_])%reif _ (fun x => orb (fst x) (negb (snd x))).
    
    Definition fork2 a : circuit( zero + [:a]) ([:a] + [:a]) := Plug  (fun x => match x with _ => inr  [!a]end).
    Definition fork2' a : circuit( [:a]) ([:a] + [:a]) := Plug  (fun x => match x with _ =>  [!a]end).
    
    Instance realise_fork2 a  : 
      Implement (fork2 a) ( _ & [b: _ ])%reif ( [b: _] & [b: _ ] )%reif (fun x => (snd x,snd x)). 
    Proof.
      unfold fork2;plug_auto. 
    Qed.
    
    Instance realise_fork2' a  : 
      Implement (fork2' a) ([b: _ ])%reif ( [b: _] & [b: _ ] )%reif (fun x => (x,x)). 
    Proof.
      unfold fork2';plug_auto. 
    Qed.
    Definition Hamlet x : circuit zero [:x] :=
      @Loop _ zero [:x] [:x]  (fork2 x |> ORNOT x x x |> fork2' x). 
    
    Lemma Implement_Hamlet x  : Implement (Hamlet x)  _ _ (fun _ => true).
    Proof. 
      intros ins outs H. 
      unfold Hamlet in H. 
      apply inversion_Loop in H; destruct H as [retro H].
      rinvert. realise_all.
      match goal with 
        | H : context [@reify ?a ?b (Reify_sum _ ?r ?r' ) (app ?x ?y)] |- _ => 
          rewrite (reify_app r r') in H
      end. 
      unreify_all bool.  
      intros_all. intros _.  intros -> . intros -> ->.   simpl. 
      destruct (snd ins0); reflexivity. 
    Qed.
  End t. 
End hamlet. 

(** The so-called hamlet circuit, in the Prop model *)
Module hamletProp. 
  Section t. 
    Context {tech : Techno}. 
    Context (tech_spec : Technology_spec tech Prop).
    
    Variable ORNOT : forall a b out, circuit ([:a] + [:b]) [:out].

    Notation "[p: x ]" := (Reify_tag Prop x).
    
    Hypothesis realise_ornot : forall a b out, Implement (ORNOT a b out) ([p: _] & [p:_])%reif _ (fun x =>  (fst x) \/ ( ~ (snd x))).
    
    Definition fork2 a : circuit( zero + [:a]) ([:a] + [:a]) := Plug  (fun x => match x with _ => inr  [!a]end).
    Definition fork2' a : circuit( [:a]) ([:a] + [:a]) := Plug  (fun x => match x with _ =>  [!a]end).
    Instance realise_fork2 a  : 
      Implement (fork2 a) ( _ & [p: _ ])%reif ( [p: _] & [p: _ ] )%reif (fun x => (snd x,snd x)). 
    Proof.
      unfold fork2;plug_auto. 
    Qed.
    
    Instance realise_fork2' a  : 
      Implement (fork2' a) ([p: _ ])%reif ( [p: _] & [p: _ ] )%reif (fun x => (x,x)). 
    Proof.
      unfold fork2';plug_auto. 
    Qed.
    
    
    Definition HamletProp x : circuit zero [:x] :=
      @Loop _ zero [:x] [:x]  (fork2 x |> ORNOT x x x |> fork2' x). 
    
    Lemma Implement_HamletProp x :  DataAbstraction (HamletProp x)  _ [p:x] (fun ins outs => outs <-> True).
    Proof. 
      intros ins outs H. 
      unfold HamletProp in H. 
      apply inversion_Loop in H; destruct H as [retro H].
      rinvert. realise_all.
      match goal with 
        | H : context [@reify ?a ?b (Reify_sum _ ?r ?r' ) (app ?x ?y)] |- _ => 
          rewrite (reify_app r r') in H
      end. 
      unreify_all Prop.  
      intros_all. intros _.  intros -> . intros -> ->.   simpl. 
    Abort. 
  End t. 
End hamletProp. 