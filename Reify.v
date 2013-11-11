(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Axioms Common Finite Data Vector Sumn Word. 

Class Iso (A B : Type) := mk_iso
  {
    iso : A -> B;
    uniso : B -> A
  }.

Implicit Arguments mk_iso [A B].
(** We separate the properties and the definition of the function  *)
Class Iso_Props {A B: Type} (I : Iso A B):= mk_iso_props
  {
    iso_uniso : forall x, iso (uniso x) = x;
    uniso_iso : forall x, uniso (iso x) = x
  }.


(** Operations on Isomorphisms  *)
Section ops. 
  Variable A B A' B' : Type.

  Definition Iso_id : Iso A A := 
    {| iso := id; uniso := id |}.
  
  Global Instance Iso_Props_id : Iso_Props Iso_id.
  Proof. 
    constructor; intros; reflexivity.
  Qed. 

  Definition Iso_prod (I : Iso A A') (J : Iso B B') :
    (Iso (A*B) (A'*B')) :=
    {| 
      iso := fun x => (iso (fst x), iso (snd x));
      uniso := fun x => (uniso (fst x), uniso (snd x))
        |}.
  
  Global Instance Iso_Props_prod {I J} {HI : Iso_Props I} {HJ: Iso_Props J}:
    Iso_Props (Iso_prod I J).
  Proof. 
    constructor. 
    intros [x y]; simpl; do 2 rewrite iso_uniso; reflexivity.
    intros [x y]; simpl; do 2 rewrite uniso_iso; reflexivity.
  Qed.

  Definition Iso_sym (I: Iso A A') : Iso A' A :=
    {| iso := uniso; uniso := iso|}.
  Global Instance Iso_Props_sym  {I}{HI : Iso_Props I}:
    Iso_Props (Iso_sym I).
  Proof. 
    constructor;intros; simpl.
    apply uniso_iso. 
    apply iso_uniso. 
  Qed.
End ops. 

Implicit Arguments Iso_sym [A A']. 
Implicit Arguments Iso_prod [A B A' B']. 

Definition Iso_compose {A B C} (ab : Iso A B) (bc : Iso B C) : Iso A C :=
  {|
    iso := fun x => iso (iso x);
    uniso := fun x => uniso (uniso x)
  |}.

Instance Iso_Props_compose {A B C : Type} (ab : Iso A B) (bc : Iso B C)(Hab : Iso_Props ab) (Hbc : Iso_Props bc) : 
  Iso_Props (Iso_compose ab bc).
Proof. 

  constructor; intros; simpl. 
  do 2 rewrite iso_uniso. reflexivity. 
  do 2 rewrite uniso_iso. reflexivity. 
Qed.

(** We first define the isomorphims, when the left member as type 
    [X -> Data] 
*)
Section t. 
  Context (Data : Type).
  Obligation Tactic := idtac. 
    
  Program Definition Iso_zero : Iso (zero -> Data) unit := 
    {|
      iso   := fun _ => tt;
      uniso := fun _ x => match x with end 
    |}.
  
  Instance Iso_Props_zero : Iso_Props Iso_zero. 
  Proof. 
    constructor. 
    intros []; reflexivity. 
    intros; apply functional_extensionality. intros []. 
  Qed.

  Program Definition Iso_unit : Iso (unit -> Data) Data := 
    {|
      iso   := fun f => f tt;
      uniso := fun e x => match x with | tt => e end 
    |}.
  
  Instance Iso_Props_unit : Iso_Props Iso_unit. 
  Proof. 
    constructor. 
    intros x; reflexivity. 
    intros; apply functional_extensionality. intros []. reflexivity. 
  Qed.
  
    
  Definition Iso_tag x : Iso ([:x] -> Data) Data:=
    {|
      iso := fun f => f [!x];
      uniso := fun f x => f
    |}.

  Instance Iso_Props_tag {x}: Iso_Props (Iso_tag x). 
  Proof. 
    constructor. 
    intros; reflexivity. 
    intros; apply functional_extensionality. intros []. reflexivity. 
  Qed.
  
  Section sum. 

    Context {A B A' B' : Type}.
    Context (IA : Iso (A -> Data) A') (IB : Iso (B -> Data) B').
    Definition Iso_sum : Iso (A + B -> Data) (A' * B') :=
      {|
        iso := fun X : A + B -> Data => 
          (iso (select_left X), iso (select_right X));
        uniso := fun x : A' * B' =>let (a, b) := x in
          app (uniso a) (uniso b)
      |}.
    
    Context {IPA : Iso_Props IA}.
    Context {IPB : Iso_Props IB}.
    Instance Iso_Props_sum : Iso_Props (Iso_sum). 
    Proof. 
      constructor. 
      intros [a b]. simpl. 
      rewrite left_app, right_app, 2 iso_uniso.  reflexivity. 
      
      intros; simpl.  
      rewrite 2 uniso_iso. rewrite <- Data.expand. reflexivity. 
    Qed.
  End sum. 
  
  Section sumn. 
    Context {A A'  : Type}.
    Context (IA : Iso (A -> Data) A').

    Fixpoint Iso_sumn (n : nat) : Iso (sumn A n -> Data) (vector A' n) :=
      match n with 
        | O => Iso_zero
        | S p => Iso_sum IA (Iso_sumn p)
      end. 
    
    Context {IPA : Iso_Props IA}.
    
    Instance Iso_Props_sumn {n}: Iso_Props (Iso_sumn n). 
    Proof. 
      induction n. simpl.
      apply Iso_Props_zero.  
      apply Iso_Props_sum. auto. 
      apply IHn. 
    Qed.
  
  End sumn.         
End t. 

(** Isomorphisms between streams. The base case are subsumed by the
above definitions *)

Section stream. 
  

  Definition vector_lift {A} n : vector (stream A) n -> stream (vector A n) :=
    fun f t => Vector.map (fun g => g t) n f. 
  Definition product_lift {A B} : stream A * stream B -> stream (A * B) :=
    fun ab t => (fst ab t, snd ab t).
  Context (A B : Type).
  
  Definition Iso_prod_stream : Iso (stream A * stream B) (stream (A * B)) :=
    {| 
      iso := product_lift;
      uniso := fun X => (fun t => fst (X t) , fun t => snd (X t))
        |}.
  Instance Iso_Props_prod_stream : Iso_Props (Iso_prod_stream). 
  Proof. 
    constructor. 
    intros. apply functional_extensionality. intros t. 
    compute. destruct ( x t ); reflexivity. 
    
    intros [a b]. simpl. 
    reflexivity. 
  Qed.

  Fixpoint vector_unlift n : stream (vector A n) -> vector (stream A) n :=
    match n with 
      | O =>  fun _ => tt
      | S p => fun X => (fun t => fst (X t), 
        vector_unlift p (Stream.map  (@snd A (vector A p) ) X) )
    end. 
  
  Definition Iso_vector_stream n : 
    Iso  (vector (stream A) n) (stream (vector A n)) :=
    {| 
      iso := vector_lift n;
      uniso := vector_unlift n
    |}.

  Instance Iso_Props_vector_stream {n}: Iso_Props (Iso_vector_stream n). 
  Proof. 
    constructor. 
    induction n;
    simpl; intros x;apply functional_extensionality. 
    intros t. destruct (x t); reflexivity.
    
    intros t. simpl. 
    simpl in IHn. rewrite IHn. compute. destruct (x t). reflexivity. 
  
    induction n.
    simpl. intros []. reflexivity. 
  
    simpl. intros [t q]; simpl. 
    simpl in IHn. 
    unfold Stream.map. simpl.
    rewrite IHn. 
    reflexivity. 
  Qed.

End stream. 

Section word.
  Require Word .
  Definition Iso_word n : Iso (vector bool n) (Word.word n) :=
    {|
      iso := Word.wordify n;
      uniso := Word.vecify n
    |}.
  
  Global Instance Iso_Props_word {n} : Iso_Props (Iso_word n).
  Proof. 
    constructor. 
    intros; simpl.
    apply Word.wordify_vecify_id. 
    apply Word.vecify_wordify_id. 
  Qed.


  (** The isomorphism from the paper, named Phi *)
  Definition Iso_Phi x  n : Iso (sumn [:x] n -> bool) (Word.word (n) ) :=
    Iso_compose (Iso_sumn bool (Iso_tag bool x) n) (Iso_word n).

  Global Instance Iso_Props_Phi {x n} : Iso_Props (Iso_Phi x n).
  Proof. 
    unfold Iso_Phi.
    apply Iso_Props_compose.
    apply Iso_Props_sumn.
    apply Iso_Props_tag.
    apply Iso_Props_word. 
  Qed. 

End word. 

Notation "'Phi'" := (Iso_Phi ) : reify_scope.    
Notation " A * B " := (Iso_prod A B) : reify_scope.  
    
(** The class Reify is a handler for automatic inference *)

Class Reify A B := reify_ :> Iso A B. 

Definition reify {A B }{R : Reify A B} (x: A) : B := iso x. 

Definition Reify_Sum {Data A B A' B'}
  (IA : Reify (A -> Data) A') 
  (IB : Reify (B -> Data) B') := Iso_sum Data IA IB.

Section selectors. 
  Context {A B Data A' B':  Type}. 
  Context (Ra : Reify (A -> Data) A').
  Context (Rb : Reify (B -> Data) B').  
  Let l := Reify_Sum Ra Rb. 
  Lemma reify_left (x : A + B ->  Data) : 
    @reify _ _ Ra (select_left x) = fst (@reify _ _ l x).
  Proof.
    reflexivity. 
  Qed.

  Lemma reify_right (x : A + B ->  Data) : 
   @reify _ _ Rb (select_right x) = snd (@reify _ _  l x).
  Proof.
    reflexivity. 
  Qed.

  Lemma reify_app (x : A ->  Data ) (y: B -> Data) : @reify _ _ l (Data.app x y) = (@reify _ _ Ra x , @reify _ _  Rb y). 
  Proof.
    compute.
    rewrite (eta_expansion x). 
    rewrite (eta_expansion y). 
    reflexivity.    
  Qed.
  
End selectors. 
(*
Section selectors'. 
  Context {a b  ra rb Data: Type}. 
  Context {Ra : Reify a (stream Data) (stream ra)}.
  Context {Rb : Reify b (stream Data) (stream rb)}.
  Local Instance l' : Reify (a + b) (stream Data) (stream (ra * rb)) := (Reify_Sum_Stream Data  Ra Rb).  
  Lemma reify_app_stream (x : a -> stream Data ) (y: b -> stream Data) : reify (Data.app x y) = Stream.zip (reify x) (reify y). 
  Proof.
    compute. 
    apply functional_extensionality. intros t. 
    rewrite <- eta_expansion. 
    rewrite <- eta_expansion. 
    reflexivity. 
  Qed.
End selectors'. 
    
Section selectors''. 
  Context {a b  ra rb Data: Type}. 
  Context {Ra : Reify a (stream Data) (stream ra)}.
  Context {Rb : Reify b (stream Data) (stream rb)}.
  
  (* Reify_Sum_Stream Data  Ra Rb).   *)
  Lemma product_lift_eq  
    (x : a -> stream Data ) 
    (y : b -> stream Data) : 
    product_lift (@reify _ _ _ (Reify_Sum _ Ra Rb) (Data.app x y)) = 
     (@reify _ _ _ (Reify_Sum_Stream _ Ra Rb) (Data.app x y)).
  Proof. 
   reflexivity. 
 Qed.
End selectors''. 
    
*)  

(** We declare canonical instances of reify for automatic reification *)
Section instances.   
  Context (Data : Type) {A A' B B' : Type}.
  Context (RA : Reify (A -> Data) A').
  Context (RB : Reify (B -> Data) B').
  Global Instance Reify_sum : Reify (A + B -> Data) (A'* B') :=
    @Reify_Sum Data A B A' B' RA RB. 

  Global Instance Reify_zero : Reify (zero -> Data) unit := 
    Iso_zero Data. 
  Global Instance Reify_tag x : Reify ([:x] -> Data) Data := 
    Iso_tag Data x. 
  Global Instance Reify_sumn n:  Reify (sumn A n -> Data) (vector A' n) := 
    Iso_sumn Data RA n. 
End instances. 

Delimit Scope reify_scope with reif.

Arguments Scope Reify_tag [type_scope string_scope]. 
Notation "[b: x ]" := (Reify_tag bool x) : reify_scope.
Notation "[!]" := (Reify_zero _) : reify_scope.
Notation "x & y" := (Reify_sum _ x y) (at level 50) : reify_scope.
Notation "[ n %- r ]" := (Reify_sumn _ r n) : reify_scope.

(* (* The special notations for the streams *) *)
(* Notation "[bs: x ]" := (Reify_Tag (stream bool) x) : reify_scope. *)
(* Notation "x &s y" := (Reify_Sum_Stream _ x y) (at level 50) : reify_scope. *)
(* Notation "[s: n %- r ]" := (Reify_Sumn_Stream _ n _ _ r) : reify_scope. *)

(*
Section test. 
  Require Import String. 
  Local Open Scope reify_scope. 
  Check (Reify_tag bool). 
  Check  [b: "x"] . 
  Check  [b: "x"] & [b: "y"] . 
  Check  [b: "x"] & [b: "y"] & [!].
  Check  [b: "x"] & [b: "y"] & [b: "c"] & [b: "d"].
  Check  [12 %- [b: "x"]]  & [b: "y"]. 
  Variable n : nat. 
  Check  [n %- ([b: "x"] & [b: "y"])]  & [b: "y"]. 
  Check  [n %- ([b: "x"] & [b: "y"])]  & [b: "sel"]. 
End test. *)

  

Ltac reify_data_simplification := idtac.

Lemma iso_prod : forall A B C D Data e (x : Iso (A -> Data) B)  ( y : Iso (C -> Data) D), 
  @iso _ _ (x & y)%reif e = (iso (Data.select_left e) , iso (Data.select_right e)).
Proof. 
  intros. 
  simpl. reflexivity. 
Qed.

Notation iso_sumn Data I n := (@iso _ _  (Iso_sumn Data I n)).

Lemma first_iso_sumn A A' Data (I : Iso (A -> Data) A') : 
  forall n p x, firstn n p (iso_sumn Data I (n+p) x) =
    iso_sumn Data I n (Data.select_left (Data.lift (Sumn.sumn_add _ n p ) x)).
Proof. 
  induction n; intros.  simpl. reflexivity.
  simpl. 
  f_equal.  rewrite ? IHn; reflexivity. 
Qed.

Lemma skipn_iso_sumn A A' Data (I : Iso (A -> Data) A') : 
      forall n p x, skipn n p (iso_sumn Data I (n+p) x) =
        iso_sumn Data I p (Data.select_right (Data.lift (Sumn.sumn_add _ n p ) x)).
Proof. 
  induction n; intros. 
  simpl. f_equal.
  simpl;  rewrite IHn;   f_equal. 
Qed.

Lemma append_iso_sumn A A' Data (I : Iso (A -> Data) A') : 
forall n p x, 
  iso_sumn Data I (n + p)  (Data.lift (Sumn.sumn_add' _ n p ) x)
  = 
  Vector.append _ _
(  iso_sumn Data I n  (select_left x))
(  iso_sumn Data I p  (select_right x)).
Proof.  
  induction n; intros. 
  simpl; f_equal.
  
  simpl in x. simpl. f_equal.  
  set (y := app (select_right (select_left x)) (select_right x)).
  specialize (IHn p y).  
  etransitivity; [etransitivity;[| apply IHn]| f_equal];
  instantiate;  f_equal. 
  apply functional_extensionality. intros.  
  unfold lift. subst y.
  unfold app, select_right, select_left. 
  
  destruct (sumn_add' A n p x0); reflexivity.
Qed. 


Ltac diff A B :=
  try ((constr_eq A B; fail 2) || idtac).

Ltac cast x BC :=
  match type of BC with 
    Iso ?B ?C =>
        match goal with 
          |- context [@reify ?A B ?AB x ] =>
            match goal with 
              |- context [@reify A C ?AC x] =>
                replace (@reify A C AC x) with (@iso B C BC (@reify A B AB x))
            end
        end
  end.

