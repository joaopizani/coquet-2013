(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Common Axioms Base Finite. 

Section Lifting. 

  Context {tech : Techno}.
  Context {Data : Type}.
  Context {tech_spec : Technology_spec tech Data}.
  Context {tech_spec' : Technology_spec tech (stream Data)}.

  (**  A wf_atom is one that can be lifted (does not depend on time) *)
  Definition wf_atom n m (c : techno n m) := 
    forall ins outs (H : spec c ins outs) (t : nat),
      spec c (time ins t) (time outs t).

  (** A wf circuit can be lifted to streams *)
  Inductive wf : forall n m (c : circuit n m), Prop :=
  | wf_Atom : forall n m t {Hn : Fin n} {Hn : Fin m} ,
      wf_atom n m t -> wf n m (Atom t)
  | wf_Ser : forall n m p x1 x2, wf n m x1 -> wf m p x2 -> wf n p (x1 |> x2)
  | wf_Par : forall n m p q x1 x2, wf n p x1 -> wf m q x2 -> wf (n + m) (p + q) 
    (x1 & x2)
  | wf_Plug : forall n m f  {Hn : Fin n} {Hn : Fin m} , wf n m (Plug f).
  
  Lemma lifting n m (x : circuit n m) (Hwf : wf n m x): forall ins outs,
    Semantics x ins outs -> forall t, Semantics x (time ins t) (time outs t).
  Proof.
    induction x; intros; rinvert; inversionK Hwf. 
    
    apply inversion_Atom in H;  constructor; auto. 

    apply IHx1 with( t := t) in Hk; clear IHx1; auto.
    apply IHx2 with (t := t) in Hk0; clear IHx2;auto.
    econstructor; eauto. 

    apply IHx1 with( t := t) in Hk; clear IHx1;auto. 
    apply IHx2 with (t := t) in Hk0; clear IHx2;auto. 

    rewrite Data.time_left in *. 
    rewrite Data.time_right in *. 
    constructor;    auto. 

    apply inversion_Plug in H. rewrite H. 
    rewrite Data.time_lift. 
    simpl. constructor. 

  Qed.
End Lifting. 