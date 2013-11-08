(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Axioms Data Sumn Finite Reify. 

Class Techno := techno : 
  forall (a b : Type), Type.

(* C'est important de separer la definition de l'inductif de sa
specification *)

Class Technology_spec (tech : Techno) A:= 
    spec : forall {a b: Type}(* {Hfa: Fin a} {Hfb : Fin b},    *),
      tech a b  -> (a -> A)  -> (b -> A) -> Prop.

Require Import Eqdep.

(* Depending on the setting, this axiom could get rid off.  *)
Ltac inversionK H := 
  inversion H;
    repeat (try subst; match goal with 
                         |H:  existT _ _ _ = existT _ _ _  |- _  => apply inj_pair2 in H
                       end);
    subst; try clear H.

Section t.
  Context {tech : Techno}.
  Context {Data : Type}.
  Context {tech_spec : Technology_spec tech Data}.

  Inductive circuit  : Type -> Type -> Type :=
  | Atom : forall {n} {m} {Hfn : Fin n} {Hfm : Fin m},
    techno n m -> circuit n m
  | Ser : forall {n m p},
    circuit n m -> 
    circuit m p -> 
    circuit n p
  | Par : forall {n m p q},   
    circuit n p -> circuit m q -> 
    circuit (n + m) (p + q)
  | Plug : forall {n m} {Hfn : Fin n} {Hfm : Fin m} (f : m -> n), 
    circuit n m
  | Loop : forall {n m l : Type},
    circuit (n + l) (m + l) ->
    circuit n m.


  Definition circuit_Fin : forall n m (x : circuit n m), (Fin n * Fin m). 
  Proof. 
    induction 1; intuition.
    apply (Fin_sum_left _ _ a). 
    apply (Fin_sum_left _ _ b). 
  Defined.

  Global Instance circuit_fin_l {n m} {x : circuit n m} : Fin n. 
  Proof.
    apply circuit_Fin in x; destruct x as [x _]; apply x. 
  Defined.
  
  Global Instance circuit_fin_r {n m} {x : circuit n m} : Fin m. 
  Proof. 
    apply circuit_Fin in x; destruct x as [_ x]; apply x. 
  Defined.
    
  Inductive Semantics : forall {n} {m}, circuit n m -> (n -> Data) -> (m -> Data) -> Prop :=
  | KAtom : forall n m {Hfn : Fin n} {Hfm : Fin m}
    (t : techno n m) ins outs, 
    spec t ins outs ->
    Semantics (Atom t) ins outs
  | KSer : forall n m p (x : circuit n m) (y : circuit m p) ins middles outs,
    Semantics x ins middles -> 
    Semantics y middles outs -> 
    Semantics (Ser x y) ins outs
  | KPar : forall n m p q (x : circuit n p) (y : circuit m q) ins outs,
    Semantics x (select_left ins) (select_left outs) ->
    Semantics y (select_right ins) (select_right outs) ->
    Semantics (Par x y) ins outs
  | KPlug : forall n m {Hfn : Fin n} {Hfm : Fin m}(f : m -> n) ins,
    Semantics (Plug f) ins (Data.lift f ins)
  | KLoop : forall n m l (x : circuit (n + l) (m + l)) ins outs retro, 
    Semantics x (Data.app ins retro) (Data.app outs retro) -> 
    Semantics (Loop x) ins outs
    .

  Lemma inversion_Loop n m l (x : circuit (n + l) (m+l)) ins outs 
    (H: Semantics (Loop x) ins outs):
    exists retro, (Semantics x (Data.app ins retro) (Data.app outs retro)). 
  Proof. 
    inversionK H. 
    exists retro; auto.  
  Qed.

  Lemma inversion_Ser n m p (x : circuit n m) (y : circuit m p) ins outs (H: Semantics (Ser x y) ins outs):
    exists middles, (Semantics x ins middles /\ Semantics y middles outs).
  Proof. 
    inversionK H. 
    exists middles; auto.  
  Qed.
  Lemma inversion_Atom n m {Hfn : Fin n} {Hfm : Fin m} (t : techno n m) ins outs (H: Semantics (Atom t) ins outs):
    spec t ins outs.
  Proof. 
    now (inversionK H). 
  Qed.
  Lemma inversion_Par n m p q  (x : circuit n p) (y : circuit m q) ins outs 
    (H: Semantics (Par x y) ins outs):
    Semantics x (select_left ins) (select_left outs)/\
    Semantics y (select_right ins) (select_right outs).    
  Proof. 
    inversionK H. split; assumption.  
  Qed.
  Lemma inversion_Plug n m {Hfn : Fin n} {Hfm : Fin m}(f : m -> n) ins outs
    ( H: Semantics (Plug f) ins outs):
    outs = Data.lift f ins. 
  Proof. 
    inversionK H. 
    reflexivity. 
  Qed.

  (* The relationnal model *)
  Class Subspec  {n} {m}
    (c : circuit n m) 
    (P : forall (i : n -> Data) (o : m -> Data), Prop) :=
  _subspec : forall i o, Semantics c i o -> P i o.

  (* The relationnal reified model  *)
  Class Realise 
    {n m} 
    (c : circuit n m) 
    {N M}
    (Rn : Reify (n -> Data) N)
    (Rm : Reify (m -> Data) M)
    (R : N -> M -> Prop)
    :=
    _realise : forall (ins : n -> Data) (outs : m -> Data), Semantics c ins outs ->
      R (reify ins)  (reify outs).

  (* The complete model *)
  Class Implement 
    {n m} 
    (c : circuit n m) 
    {N M}
    (Rn : Reify (n->Data) N)
    (Rm : Reify (m->Data) M)
    (f : N -> M)
    :=
    implement : forall ins outs, Semantics c ins outs ->
      reify outs = f (reify ins).


  (* A combinator that is only the identity *)
  Definition ONE (t : Type) {f : Fin t}: circuit t t := Plug id.

  Global Instance ONE_subspec {t} {f : Fin t}: Subspec (ONE t)
  (fun i o => o = i).
  Proof. 
    unfold Subspec, ONE. 
    intros; apply inversion_Plug in H.
    rewrite H. 
    unfold Data.lift. 
    rewrite eta_expansion. reflexivity.
  Qed.

  Global Instance ONE_Implement {x} {f : Fin x} {x'}
    (ra : Reify (x -> Data) x'): Implement (ONE x) ra ra (id).
  Proof. 
    intros ins outs H. 
    apply inversion_Plug in H. 
    rewrite H. clear H. 
    compute. 
    f_equal.
    Require Import Axioms. apply  functional_extensionality; reflexivity.  
  Qed.

  

  Definition Rewire 
    {n m N M: Type}
    {Fn : Fin n}
    {Fm : Fin m}
    {Rn : Reify (n->Data) N}
    {Rm : Reify (m->Data) M}
    (g:m -> n)
    (f:N -> M) 
    (H : Implement (Plug g) _ _ f)
    : circuit n m :=
    Plug g.
  Global Instance Rewire_Implement 
    {n m N M: Type}
    {Fn : Fin n}
    {Fm : Fin m}
    {Rn : Reify (n->Data) N} 
    {Rm : Reify (m->Data) M}
    {g:m -> n}
    {f:N -> M}
    {H : Implement (Plug g) _ _ f}
    : Implement (Rewire  g f H) Rn Rm (f).
  Proof. 
    unfold Rewire. 
    apply H. 
  Qed.  
  Definition RewireE 
    {n m N M: Type}
    {Fn : Fin n}
    {Fm : Fin m}
    (Rn : Reify (n->Data) N)
    (Rm : Reify (m->Data) M)
    (g:m -> n)
    (f:N -> M) 
    (H : Implement (Plug g) _ _ f)
    : circuit n m :=
    Plug g.
  Global Instance RewireE_Implement 
    {n m N M: Type}
    {Fn : Fin n}
    {Fm : Fin m}
    {Rn : Reify (n->Data) N} 
    {Rm : Reify (m->Data) M}
    {g:m -> n}
    {f:N -> M}
    {H : Implement (Plug g) _ _ f}
    : Implement (RewireE  Rn Rm g f H) Rn Rm (f).
  Proof. 
    unfold Rewire. 
    apply H. 
  Qed.  

End t.

Notation " x |> y " := (Ser  x y) (at level 61).
Notation " [ x ] " := (Atom x).
Notation " x & y" := (Par x y)(at level 50).
  
  
(* Rewrite an hypothesis as much as possible, and clear it.
   All specs should be written as [P outs === Q ins]
 *)
Ltac bang H :=
  rewrite ! H; clear H. 

(* Invert the goal   *)
Ltac rinvert :=
  repeat match goal with 
           | H : Semantics (Ser ?x ?y) ?i ?o |- _ =>
             apply inversion_Ser in H;
             destruct H as [?mid [?Hk ?Hk]]
           | H : Semantics (Par ?x ?y) ?i ?o |- _ =>
             apply inversion_Par in H;
             destruct H as [?Hk ?Hk]        
         end.

Ltac realise_all :=
  repeat match goal with 
           | H : Semantics (Rewire ?g ?f _) ?i ?o |- _ =>
             apply  Rewire_Implement in H
           | H : Semantics (RewireE ?rn ?rm ?g ?f _) ?i ?o |- _ =>
             apply  RewireE_Implement in H
           | H : Semantics ?x ?i ?o |- _ =>
             apply implement  in H
         end;
  reify_data_simplification.


Ltac lebon x :=
  match goal with 
    | |- context [@reify  _ _ ?r x] => constr:r
    | |- _ => 
      match x with 
        | select_left ?y => 
          match lebon y with 
            | Reify_sum _ ?R _ => constr:R
          end
        | select_right ?y => 
          match lebon y with 
            | Reify_sum _ _ ?R => constr:R
          end
      end
  end.

Ltac levelling  :=
  match goal with
  |- context [@reify _ _ ?e (Data.select_left ?x)] =>
    let r := lebon x in 
      replace (@reify _ _ e (Data.select_left x))
  with 
    (fst (@reify _ _  r x))
    by (clear ; symmetry;apply reify_left)
   | |- context [@reify _ _ ?e (Data.select_right ?x)] =>
    let r := lebon x in 
    replace (@reify _ _ e (Data.select_right x))
  with 
    (snd (@reify _ _  r x))
    by (clear ; symmetry;apply reify_right)
end.

Ltac unreify x :=
  match goal with 
    |- context [@reify ?a ?b ?r ?e] =>
      match e with 
        | context [x] =>  generalize (@reify a b r e);
          let x' := fresh x in intros x'
      end
  end;
  clear x.

Ltac unreify_all data :=
  repeat match goal with
           | x : ?t -> data |- _ => 
             revert dependent x; 
             intros x;
             repeat levelling;
             first [unreify x]
           end. 
  
Ltac destruct_all :=
  repeat match goal with 
           X : (?x * ?y)%type |- _ => destruct X
         end.

Ltac intros_all :=
  repeat first  [intros -> | intros H; injection H; clear H].

Ltac unreify'' e:=
    revert dependent e;
intros e;
  let e1 := fresh "el1" in 
    let e2 := fresh "el2" in 
      let H := fresh in 
        (match goal with 
           |- context [@reify ?x ?y ?tgt1 ?R e] => 
             set (e1 := @reify x y tgt1 R e);
               match goal with 
                 |- context [@reify ?x ?y ?tgt2 ?R e] => 
                   set (e2 := @reify x y tgt2 R e);
                     try assert (H : e2 = e1)
               end
         end).

Ltac plug_def :=
  repeat 
    match goal with 
      | |- _ + _ -> _ => 
          let x := fresh in intros [x | x]; revert x
      | |- _ -> _ => intros ?
    end; auto.

Ltac plug_auto :=
  match goal with 
    |- Implement (Plug ?f) _ _ ?g  => 
      intros ins outs H;
        apply inversion_Plug in H;
          rewrite H; reflexivity
  end.
