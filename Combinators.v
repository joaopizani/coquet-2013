(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Axioms Common Base Finite Sumn  Reify. 
 

Section Fork. 
  Context {t : Techno}.
  Context {A  Data A' : Type} {fi : Fin A}.
  Context {Ra : Reify.Reify (A -> Data) A'}.
  Context {spec : Technology_spec t Data}.
  
  Definition Fork n : circuit A (sumn A n) := 
    Plug (Sumn.sumn_repeat A n).
  
  Global Instance Fork_Implement {n}: 
    Implement  (Fork n) _ ([n %- Ra])%reif  (fun x => Vector.vector_repeat n x).
  Proof. 
    intros ins outs H.
    apply inversion_Plug in H.
    rewrite H. clear. 
    induction n. 
    reflexivity.
    replace (Data.lift (sumn_repeat A (S n)) ins) with 
      (Data.app ins (Data.lift (sumn_repeat A n) ins)).
    
    match goal with 
      |- context [@reify ?a ?b  ?r (Data.app ?x ?y)] => 
        replace (@reify a b  r (Data.app x y)) with 
          (reify x, reify y) by (symmetry; rewrite <- reify_app; reflexivity)
         end.
    simpl. f_equal. apply IHn. 
  
    clear.
    unfold Data.app, Data.lift. 
    apply functional_extensionality. 
    intros [x|x]; reflexivity. 
  Qed.
End Fork. 

Section Fork2. 
  Context {t : Techno}.
  Context (A : Type) {Data A' : Type} {fi : Fin A}.
  Context {Ra : Reify.Reify (A -> Data) A'}.
  Context {spec : Technology_spec t Data}.
  
  Definition Fork2 : circuit A (A + A) := 
    Plug (fun x => match x with inl e => e | inr e => e end).
  
  Global Instance Fork2_Implement : 
    Implement  (Fork2) _ (Ra & Ra)%reif  (fun x =>( x,x) ).
  Proof. 
    unfold Fork2. intros ins outs H. 
    apply inversion_Plug in H.
    rewrite H. compute. 
    rewrite (eta_expansion ins).
    reflexivity. 
  Qed.
End Fork2. 

Section bin_tree. 
  Context {t : Techno}.
  Context {n m : Type} {fn : Fin n} {fm : Fin m}.
  
  Variable cell : circuit (n + n) n . 

  Fixpoint pow2 k := match k with O => 1 | S p => pow2 p + pow2 p end.
  Fixpoint bin_tree k : circuit (sumn n (pow2 k)) n :=
    match k with 
      0 => Plug  (fun x => match x with | inl e => inl  e | inr e => inl  e end)       |> cell  
        
      | S p => 
        Plug (sumn_add _ _ _ ) |> (bin_tree p & bin_tree p )|> cell
    end.   
End bin_tree.

Section map. 
  Context {t : Techno}.
  Context {Data : Type}.
  Context (tech_spec : Technology_spec t Data).

  Context {n m : Type} {fn : Fin n} {fm : Fin m}.
  
  Variable cell : circuit n m. 

  Fixpoint map k : circuit (sumn n k) (sumn m k) :=
    match k with 
      | 0 => Plug id 
      | S p => 
        cell & (map p)
    end.  
 
  Context {N M : Type}{Rn : Reify (n -> Data) N}{Rm : Reify (m ->Data) M}.
  Context {f : N -> M}.
  Context {Hcell : Implement cell Rn Rm f}.
  Global Instance map_Implement { k} : Implement (map k) _ _ (Vector.map f k).
  Proof.
    induction k;   simpl;
    intros ins outs H.
    compute; reflexivity.
    rinvert.
    apply Hcell in Hk. apply IHk in Hk0. clear IHk.
    unreify_all Data.
    rewrite (surjective_pairing outs0). simpl.
    intros -> ->. destruct ins0. reflexivity. 
  Qed.
  Context
  {R : N -> M -> Prop}
  {Hcell' : Realise cell Rn Rm R}.
  Global Instance map_Realise {k} : Realise (map k) _ _ (Vector.pointwise R k).
  Proof. 
    induction k; simpl; intros ins outs H.
    auto. 
    apply inversion_Par in H. destruct H as [H H'].
    apply IHk in H'. 
    apply Hcell' in H. clear - H H'. 
    rinvert;realise_all.
    unreify_all Data. 
    intros. 
    destruct ins0.  destruct outs0. simpl. intuition.
  Qed. 
End map. 

Section COMPOSEN.
  Context {t : Techno}.
  Context {n: Type} {fn : Fin n}.
  
  Variable cell : circuit n n. 

  Fixpoint COMPOSEN k : circuit (n) (n) :=
    match k with 
      | 0 => Plug id 
      | S p => 
        cell |> (COMPOSEN p)
    end.  

  Fixpoint composen A (f : A -> A) n : A -> A := 
    match n with 
      | 0 => id
      | S p => fun x =>  (composen A f p (f x))
    end. 

  Context {Data : Type}.
  Context (tech_spec : Technology_spec t Data).

  Lemma COMPOSEN_Spec {A : Type} 
    (I : Iso (n -> Data) A) (f : A -> A) 
    (H : Implement cell I I f) k :
    Implement 
    (COMPOSEN k)
    I I 
    (composen A f k).
  Proof. 
    induction k;  simpl.
    clear H.  intros ins outs H. apply inversion_Plug in H.  subst.
    compute. rewrite <- (eta_expansion ins). reflexivity. 
    
    intros ins outs H'. rinvert. apply H in Hk.   apply IHk in Hk0.
    unreify_all Data. intros ->. intros ->. congruence. 
  Qed.

End COMPOSEN. 

(* Section triangle. *)
(*   Context {t : Techno}. *)
(*   Context {n: Type} {fn : Fin n}. *)
  (*   Variable cell : circuit n n.  *)
(*   Program Fixpoint triangle k : circuit (sumn n k) (sumn n k) := *)
(*     match k with  *)
(*       | 0 =>  Plug id  *)
(*       | S p =>  *)
(*         Plug _ |> *)
(*           ONE n & (map cell k |> Plug _ |> triangle p) |> Plug _  *)
(*     end.   *)
(*   Next Obligation.  *)  
(* End composeN.  *)
