(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../". 
Require Import Data EqT Common Finite Reify Base  ZArith String. 
Require Import Sumn Vector. 


 

Module Type T.
  Parameter tech : Techno. 
  Parameter tech_spec_bool : Technology_spec tech bool. 

  Existing Instance tech. Existing Instance tech_spec_bool.
  Parameter AND : forall a b out, circuit ([:a] + [:b]) ([:out]).
  Parameter OR : forall a b out, circuit ([:a] + [:b]) ([:out]).
  Parameter NOT : forall a  out, circuit ([:a]) ([:out]).
  Parameter MUX : forall n a b sel out,
    circuit (sumn [:a] n + sumn [:b] n + [:sel]) (sumn [:out] n).

  Declare Instance  AND_Implement : forall a b out, Implement (AND a b out) 
    ([b:a] & [b:b])%reif
    ([b:out])%reif
    (curry andb).
  Declare Instance OR_Implement : forall a b out,  Implement 
    (OR a b out) 
    ([b:a] & [b:b])%reif
    ([b:out])%reif
    (curry orb).
  Declare Instance NOT_Implement : forall a out,   Implement
    (NOT a out) 
    ([b:a] )%reif
    ([b:out])%reif
    (negb).
  Declare Instance MUX_Implement : forall n a b sel out, Implement 
    (MUX n a b sel out )
    ([n %- [b: a]] &  [n %- [b: b]]  & [b: sel])%reif
    ([n %- [b: out]])%reif
    (     fun x => match x with 
              | (l,r,b) => if b then l else r
            end  ).
End T. 
 
Module ADD (X : T).
  Import X. 
  Existing Instance tech. Existing Instance tech_spec_bool.

  Definition RENAME a b : circuit [:a] [:b] := Plug (fun x : [:b] => [!a]).
  Instance RENAME_Implement {a b} : 
    Implement (RENAME a b)
    ([b:a] )%reif
    ([b:b])%reif
    (id).
  Proof. 
    unfold RENAME. 
    plug_auto. 
  Qed.
  Require Import Combinators. 
  Definition RENAMES n a b : circuit (sumn [:a] n)(sumn [:b] n) := 
    map (RENAME a b) n. 
  Lemma RENAMES_Implement n a b :
    Implement (RENAMES n a b)
    (_)%reif
    (_ )%reif
    (Vector.map id n).
  Proof. 
    unfold RENAMES. 
    apply map_Implement.
    apply RENAME_Implement. 
  Qed.

  Lemma RENAMES_Implement2 n a b :
    Implement (RENAMES n a b)
    ( Iso_Phi a n )%reif
    ( Iso_Phi b n )%reif
    (id ).
  Proof. 
    intros ins outs H. 
    apply RENAMES_Implement in H.
    revert H. cast outs ( (Iso_word n)).
    intros H. 
    rewrite H.
    Lemma vector_map_id A n (x : vector A n) : Vector.map id n x = x.
      induction n; simpl. destruct x; reflexivity.  
      simpl in x. destruct x. rewrite IHn. reflexivity. 
    Qed.
    rewrite vector_map_id. 
    reflexivity. 
    reflexivity. 
  Qed.
  Definition both x nx :=
    Fork2 [:x] |> (ONE [:x] & NOT x nx).
  
  Instance Implement_both {x nx}: Implement (both x nx)
    ([b:x])%reif
    ([b:x] & [b:nx])%reif
    (fun x => (x,negb x)).
  Proof.
    intros ins outs H. 
    unfold both in H. 
    rinvert;   realise_all. 
    unreify_all bool.         
    simpl. 
    intros_all. 
    rewrite (surjective_pairing outs0). simpl. intros -> ->. 
    reflexivity. 
  Qed.

                            (***********)
                            (* ADDER_1 *)
                            (***********)

  Definition adder1_plug1 a b c d: 
    a + d + (c + b) + (a + b) + (c + d) + a + b -> a + c + (b + d).
  Proof. 
    intros. 
    intuition. 
  Defined. 

  Definition adder1_plug1' (x : bool * bool * (bool * bool)) :=
    match x with 
      | (a,c,(b,d)) => 
        (a , d , (c , b) , (a , b) , (c , d) , a , b)
    end.
  
  Instance adder1_plug1'' a b c d :
    Implement (Plug (adder1_plug1 [:a] [:b] [:c] [:d]))
    ([b: a] & [b: c]  & ([b: b]  & [b: d])  )%reif
    (_)
    (adder1_plug1').
  Proof.
    plug_auto. 
  Qed.

  Definition adder1_plug2 a b c d e f:
    a + b + c + (c + d) + (e + f) -> a + b + c + d + e + f.
  Proof. 
    intuition. 
  Defined.
  
  Definition adder1_plug2' (x : bool * bool * bool * bool * bool * bool) :=
    match x with 
      | (a,b,c,d,e,f) => 
        (a , b , c , (c , d) , (e , f))
    end.
  
  Instance adder1_plug2'' a b c d e f:
    Implement (Plug (adder1_plug2 [:a] [:b] [:c] [:d] [:e] [:f]))
    ( _)
    ( _)
      (adder1_plug2').
  Proof. 
    plug_auto. 
  Qed.

  Definition adder1 (x y s t G P : string) :
    circuit ([:x] + [:y]) ([:s] + [:G] + [:t] + [:P]) :=
    ((both x "nx" & both y  "ny")
     |> Plug (adder1_plug1 [:x] [:y] [:"nx"] [:"ny"])
       |> ( AND x "ny" "a" 
         & AND "nx" y "b" 
         & AND x y G 
         & AND "nx" "ny" "c" 
         & ONE [:x] 
         & ONE [:y]) 
       |> Plug (adder1_plug2  [:"a"] [:"b"] [:G] [:"c"] [:x] [:y])
         |> ( OR "a" "b" s & ONE [:G] & OR G "c" t & OR x y P))%string. 
 
  Definition adder1' (i : bool * bool) :=
    (let (x,y) := i in 
    let s := (x && negb y) || (negb x && y) in 
    let t := (x && y) || (negb x && negb y) in 
    let g := x && y in 
    let p := x || y in 
    (s,g,t,p))%bool.
      


  Instance Implement_adder1 x y s t G P: 
    Implement (adder1 x y s t G P)
    ([b:x] & [b:y])%reif
    ([b: s] & [b:G] & [b:t] & [b:P])%reif
    (adder1').
  Proof. 
    intros ins outs H.
    unfold adder1 in H. 
    rinvert. realise_all.     
    unreify_all bool. 
    destruct_all. simpl. 
    intros_all. 
    boolean_eq. 
  Qed.
  
  
  Definition dv_adder_plug1 : forall x y, 
    x + y -> x + zero + ( y + zero). 
  Proof. 
    intuition.
  Defined. 
  Definition dv_adder_plug1' (x : bool * unit * (bool * unit)) : bool * bool := 
    match x with 
      | (x, _,(y, _)) => (x,y)
    end. 
  Instance Implement_dv_adder_plug1  {x y}: 
    Implement 
    (Plug (dv_adder_plug1 [:x] [:y]))
    ([b:_] & [!] & ( [b: _ ] & [!]))%reif
    (_)
    dv_adder_plug1'. 
  Proof.
    plug_auto.
  Qed.

  Definition dv_adder_plug2 : forall g p s t, 
    g + p + sumn s 1 + sumn t 1 -> 
    s + g + t + p.
  Proof.
    clear; intros g p s t. 
    unfold sumn. 
    intuition.
  Defined.     
  Definition v1 x : vector bool 1:= Vector.cons  _ x (Vector.nil bool).

  Definition dv_adder_plug2' (x : bool * bool * bool * bool  )     
    :=
    match x with 
      (s , g , t , p) => (g , p , Word.wordify 1 (v1 s) , Word.wordify 1 (v1 t))
    end.

  
  Instance Implement_dv_adder_plug2  {s g t p}:
    Implement
    (Plug (dv_adder_plug2 [:g] [:p] [:s] [:t]))
    ([b:s] & [b:g] & [b:t] & [b:p]  )%reif
    ([b:g] & [b:p] & Iso_Phi _ 1  & Iso_Phi _ 1 )%reif
    dv_adder_plug2'.
  Proof.
    plug_auto. 
  Qed.

  Definition base_adder x y s t G P  : 
    circuit ([:x] + zero + ([:y] + zero))
  ([:G] + [:P] + sumn [:s] 1 + sumn [:t] 1)
  :=
    Plug (dv_adder_plug1 [:x] [:y])
    |> adder1 x y s t G P 
    |> Plug (dv_adder_plug2 [:G] [:P] [:s] [:t]).


  (** The function that the circuit implements  *)
  Definition dv_adder' n ( xy : Word.word n * Word.word n ) : bool * bool * Word.word n * Word.word n :=
    let (x,y) := xy in 
    let (g,s) := Word.carry_add n x y false in 
    let (p,t) := Word.carry_add n x y true in 
        (g,p,s,t).      

  Instance Implement_base_adder x y s t G P : Implement (base_adder x y s t G P)
    (Iso_Phi _ [2^0] & Iso_Phi _ [2^0])%reif
    (Iso_tag bool _ & Iso_tag  bool _ & Iso_Phi _ [2^0] & Iso_Phi _ [2^0])%reif
    (dv_adder' [2^0]).
  Proof. 
    intros ins outs H. 
    unfold base_adder in H. 
    rinvert.
    apply Implement_dv_adder_plug2 in Hk0. 
    realise_all.
    unreify_all bool. 
    Definition Iso_w2 : Iso (Word.word 1 * Word.word 1) (bool * unit * (bool * unit)).
    exact (Iso_sym (Iso_prod (Iso_word 1) (Iso_word 1)))%reif.
    Defined. 
    
    unfold Common.pow2. 
    cast ins (Iso_sym  Iso_w2); [| reflexivity]. 
    unreify_all bool.

    Ltac cast' x :=
    match goal with 
      |- context [@reify ?A ?B ?AB x ] =>
        match goal with 
          |- context [@reify A ?C ?AC x] =>
            diff AB AC;
            replace (@reify A C AC x) with  (@reify A B AB x) 
        end
    end.
    cast' outs;[| reflexivity]. 
    unreify_all bool. 
    destruct_all.   simpl. 
    intros_all.  apply eqT_true. clear.
    destruct b2; destruct b1; vm_compute; reflexivity.
  Qed.

                     (*************************)
                     (* Propagte and generate *)
                     (*************************)

  (* The second piece of circuitry that allows to compute the carry
     propagate and carry generate bits for the 2n adder *)

  
  Program Definition PG  gL pL gH pH g p :
    circuit ([:gL] + [:pL] + [:gH] + [:pH])
    ([:g] + [:p]) :=
    Rewire 
    _
    ( fun x => match x return _ with 
                (gL,pL,gH,pH) =>
                (pH,gL,gH,(pH,pL,gH))
              end
    )
    _
    |> 
      (
        ((AND pH gL "pHgL" & ONE [:gH]) |> OR "pHgL" gH g) &
        ((AND pH pL "pHpL" & ONE [:gH]) |> OR "pHpL" gH p)
      )
      .
  Next Obligation. 
    revert H. plug_def. 
  Defined.    
  Next Obligation. 
    plug_auto. 
  Qed.
  (* p = gH + pH pL 
     g = gH + pH gL
  *)
  Definition PG' (x : bool * bool * bool * bool):=
    (match x with 
      | (gL,pL,gH,pH) => 
        let p := gH || (pH && pL) in 
        let g := gH || (pH && gL) in 
          (g,p)
    end)%bool.
    
  Instance Implement_PG gl pl gr pr g p: 
    Implement (PG  gl pl gr pr g p)
    ([b:gl] & [b:pl] & [b:gr] & [b:pr])%reif
    ([b:g] & [b:p])%reif
    (PG').
  Proof. 
    intros ins outs H. 
    unfold PG in H.

    rinvert;realise_all.
    unreify_all bool. 
    destruct_all; simpl. intros_all. intros; subst.  
    
    clear. boolean_eq. 
  Qed.

                              (*******)
                              (* FIX *)
                              (*******)

  Program Definition Fix n s t g p :
    circuit 
    (sumn ([:s] ) n 
    +sumn ([:t] ) n 
    +[:g] + [:p])
    (sumn [:s]  n + sumn [:t]  n)
    :=
    (
     
      Rewire
      ( _ : ((sumn [:t]  n  +sumn [:s]  n  +[:g]) + 
        (sumn [:t]  n  +sumn [:s]  n  +[:p]))
        -> (sumn ([:s] ) n  +sumn ([:t] ) n  +[:g] + [:p])  
      )
      ( fun (x : vector bool n * vector bool n * bool * bool) => match x return _ with 
                  | (s,t,g,p)  => (t , s , g , (t , s ,p))
                end
      )
      _  
      |> MUX n t s g s & MUX n t s p t
    ).
  Next Obligation. 
    revert X. plug_def. 
  Defined. 
  Next Obligation.
    plug_auto.
  Qed.
  Definition Fix' n (x : vector bool n * vector bool n * bool * bool) : 
    vector bool n * vector bool n
    := 
    match x with 
      (s,t,g,p) => 
      let s' := if g then t else s in 
      let t' := if p then t else s in 
        (s',t')
    end.
  Lemma Implement_fix {n a b c d} :
    Implement (Fix n a b c d)
    ( _ )%reif 
    ( _)%reif
    ( Fix' n
    ).
  Proof. 
    intros ins outs H. 
    unfold Fix in H. rinvert. 
    apply MUX_Implement in Hk0. 
    apply MUX_Implement in Hk1. 
    
    realise_all.
    unreify_all bool. 
    repeat match goal with 
      | |- context [match ?x with pair _ _ => _ end] => 
        rewrite (surjective_pairing x)
    end.
    destruct_all. 
    simpl. 
    intros_all. 
    reflexivity. 
  Qed. 
  Definition Fix'' n (x : Word.word n * Word.word n * bool * bool) : 
    Word.word n * Word.word n
    :=   match x with 
      (s,t,g,p) => 
      let s' := if g then t else s in 
      let t' := if p then t else s in 
        (s',t')
    end.
  Lemma Implement_Fix {n a b c d} :
    Implement (Fix n a b c d)
    ( Iso_Phi _ _  & Iso_Phi _ _ & [b: _] & [b:_] )%reif 
    ( Iso_Phi _ _  & Iso_Phi _ _)%reif
    ( Fix'' n).
  Proof. 
    intros ins outs H. 
    apply Implement_fix in H. 
    revert H. 
    cast outs ( (Iso_prod(Iso_word n) (Iso_word n))); [|reflexivity].
    intros. 
    rewrite H. clear H. 
    
    
    cast ins (Iso_word n * Iso_word n * Iso_id bool * Iso_id bool)%reif;
    [|reflexivity].
    
    unreify_all bool.
    destruct_all.  simpl. 
    boolean_eq. 
  Qed.




    
                        (*******************)
                        (* RECURSIVE ADDER *)
                        (*******************)


  Definition high_low x n p :
    circuit 
    (sumn [:x] (n + p))
    (sumn [:x] n + sumn [:x] p)
    :=
    Plug     ((sumn_add _ n p)).


  Lemma Implement_high_low x n p: 
    Implement (high_low x n p)
    ( Iso_Phi x (n+p)   )%reif
    ((Iso_Phi x n & Iso_Phi x p))%reif
    (fun x => (Word.low n p x, Word.high n p x)). 
  Proof. 
    intros ins outs H. 
    apply inversion_Plug in H. 
    rewrite H.
    
    unfold reify. 
    unfold reify_. 
    
    rewrite Reify.iso_prod.
    f_equal. simpl. rewrite Word.low_wordify. 
    f_equal. rewrite first_iso_sumn. reflexivity. 

    simpl. rewrite Word.high_wordify. f_equal. 
    rewrite skipn_iso_sumn. reflexivity. 
  Qed.

  Definition combine' x n p :
    circuit 
    (sumn [:x] n + sumn [:x] p)
    (sumn [:x] (n + p))
    :=
    Plug     ((sumn_add' _ n p)).

  Lemma Implement_combine' x n p: 
    Implement (combine' x n p)
    ((Iso_Phi x n & Iso_Phi x p))%reif
    (Iso_Phi x (n + p) )%reif
    (fun x => (Word.combine n p (fst x) (snd x))). 
  Proof. 
    intros ins outs H. 
    apply inversion_Plug in H. 
    rewrite H.
    
    unfold reify. 
    unfold reify_. 
    
    rewrite Reify.iso_prod.
    
    simpl.  
    rewrite append_iso_sumn.       

    rewrite Word.wordify_combine. 
    reflexivity. 
  Qed.

  
  Definition combine x xl xr n p :
    circuit 
    (sumn [:xl] n + sumn [:xr] p)
    (sumn [:x] (n + p))
    :=
    ((RENAMES n xl x) & (RENAMES p xr x)) |>  combine' x n p.
  Lemma Implement_combine x xl xr n p: 
    Implement (combine x xl xr n p)
    ((Iso_Phi xl n & Iso_Phi xr p))%reif
    (Iso_Phi x (n + p) )%reif
    (fun x => (Word.combine n p (fst x) (snd x))). 
  Proof. 
    intros ins outs H.  unfold combine in H. 
    rinvert. apply RENAMES_Implement2 in Hk. 
    apply RENAMES_Implement2 in Hk1. 
    apply Implement_combine' in Hk0. 
    rewrite Hk0. clear Hk0.
    revert Hk Hk1. 
    repeat match goal with 
      |  |- context [fst (@reify ?a ?b (Reify_sum _ ?r ?r') ?e)] =>
        replace (fst (@reify a b _ e)) with (@reify _ _ r (select_left e))
        by (apply reify_left)
      |  |- context [snd (@reify ?a ?b (Reify_sum _ ?r ?r') ?e)] =>
        replace (snd (@reify a b _ e)) with (@reify _ _ r' (select_right e))
        by (apply reify_right)
    end. 
    
    unreify_all bool. unfold id.  
    simpl. congruence. 
  Qed. 

  Program Definition high_lows x y n p : 
    circuit 
    (sumn [:x] (n + p) + sumn [:y] (n+p))
    (sumn [:x] n + sumn [:y] n + (sumn [:x] p + sumn [:y] p)) :=
    (high_low x n p & high_low y n p) 
    |> 
    RewireE
    ((Iso_Phi x n & Iso_Phi x p) & (Iso_Phi y n & Iso_Phi y p))%reif
    ((Iso_Phi x n & Iso_Phi y n) & (Iso_Phi x p & Iso_Phi y p))%reif
    _
    (fun x => 
      let xLH := fst x in 
      let yLH := snd x in 
        ((fst xLH, fst yLH),       (snd xLH, snd yLH))
    )
    _ . 
  Next Obligation.
    revert X; intros [[? | ?] | [? | ? ]]; auto.
  Defined.
  Next Obligation. 
    plug_auto.
  Qed.

  Lemma Implement_high_lows x y n p : Implement (high_lows x y n p)
    (Iso_Phi x (n + p) & Iso_Phi y (n + p))%reif
    ((Iso_Phi x n & Iso_Phi y n) & (Iso_Phi x p & Iso_Phi y p))%reif
    (fun e => 
      match e with 
        (X,Y) =>  
        ((Word.low n p X, Word.low n p Y), (Word.high n p X, Word.high n p Y))
      end
    ).
  Proof. 
    intros ins outs H. unfold high_lows in H. 
    rinvert. apply Implement_high_low in Hk.
    apply Implement_high_low in Hk1. realise_all.
    rewrite Hk0.  clear Hk0 outs.
    clear - Hk Hk1.
    rewrite (surjective_pairing (reify ins)).
    unreify_all bool.
    intros ->. 
    intros ->. 
    simpl. congruence.
  Qed.

    Program Definition combines s t sl tl sr tr p n:
      circuit 
      ((sumn [:sl] p + sumn [:tl] p) + (sumn [:sr] n + sumn [:tr] n))
      (sumn [:s] (p + n) + sumn [:t] (p + n)) :=
      RewireE

      (Iso_Phi _ _ & Iso_Phi _ _  & (Iso_Phi _ _ & Iso_Phi _ _ ))%reif
      (Iso_Phi _ _ & Iso_Phi _ _  & (Iso_Phi _ _ & Iso_Phi _ _ ))%reif
      _
      (fun x => 
        match x return _ with 
          | (sl,sr,(tl,tr)) => (sl,tl,(sr,tr))
        end
      )
        _
      |> combine s sl sr p n & combine t tl tr p n. 
    Next Obligation. 
       repeat match goal with 
      H : (?x + ?y)%type |- ?z =>
        revert H;   intros [? | ?]
              end; auto.
     Defined.   
     Next Obligation.
       plug_auto. 
     Qed.       
    Program Definition plug_final G P s t p :=
      RewireE
      (
        [b:G] & [b:P] &( Iso_Phi s ([2^p] + [2^p]) & Iso_Phi t ([2^p] + [2^p]))
      )%reif
      (
        [b:G] & [b:P] & Iso_Phi s ([2^p] + [2^p]) & Iso_Phi t ([2^p] + [2^p])
      )%reif
      _
      (fun x => match x return _ with 
                 | (a,(b,c)) => (a,b,c)
               end
      )
      _.
    Next Obligation.
      repeat match goal with 
      H : (?x + ?y)%type |- ?z =>
        revert H;   intros [? | ?]
    end; auto.
    Defined. 
    Next Obligation.
      plug_auto. 
    Qed. 

    Require Import String. 
  Program Fixpoint dv_adder n x y s t G P :
    circuit 
    (sumn [:x][2^ n] + sumn [:y] [2^ n])
    ([:G] + [:P] + sumn [:s]  [2^ n] + sumn  [:t] [2^ n] )
    :=
    match n with 
      | 0 => base_adder x y s t G P
      | S p =>  
        high_lows x y [2^p] [2^p]
        |> ((dv_adder p x y "sL" "tL" "gL" "pL")%string
          & dv_adder p x y "sH" "tH" "gH" "pH")%string  
        |> 
          RewireE  
          (
            ([b: "gL"] & [b:"pL"] & Iso_Phi ("sL")%string [2^p] & Iso_Phi ("tL")%string [2^p])
            &  ([b: "gH"] & [b:"pH"] & Iso_Phi  ("sH")%string [2^p] & Iso_Phi ("tH")%string [2^p])
          )%reif
          (
            ([b: "gL"] & [b:"pL"] & [b: "gH"] & [b: "pH"])
            & 
            ((Iso_Phi ("sL")%string [2^p] & Iso_Phi ("tL")%string [2^p] )
              & (Iso_Phi ("sH")%string [2^p] & Iso_Phi ("tH")%string [2^p] & [b:"gL"] & [b:"pL"])
)
          )%reif
          _
          (fun x =>
            match x return _ with 
              | ((gL,pL,sL,tL),(gH,pH,sH,tH)) =>
                ((gL,pL,gH,pH),((sL,tL),(sH,tH,gL,pL)))
            end
          )
          _
        |> 
          ( PG "gL" "pL" "gH" "pH" G P 
            & 
            (
              ((ONE (sumn [:"sL"] ([2^ p])) & ONE (sumn [:"tL"] ([2^ p])))
              & Fix ([2^ p]) "sH" "tH" "gL" "pL" )
              |> combines s t "sL" "tL"  "sH" "tH" [2^p] [2^p]
            )
          )
        |>  plug_final G P s t p
     
    end.
  Next Obligation.
    revert X. plug_def. 
  Defined.
  Next Obligation.
    plug_auto. 
  Qed.

  (** The interesting part of the lemma  *)
  Lemma dv_adder_invar n m (xL yL: Word.word n) (xH yH : Word.word m) 
    (sL tL : Word.word n) (sH tH : Word.word m) g p gL pL gH pH sH' tH': 
    (gL,pL,sL,tL) = dv_adder' n (xL,yL) -> 
    (gH,pH,sH,tH) = dv_adder' m (xH,yH) ->
    (sH',tH') = Fix'' m (sH,tH,gL,pL) ->
    (g,p) = PG' (gL,pL,gH,pH) -> 
    (g,p, Word.combine n m sL sH', Word.combine n m tL tH') = 
    dv_adder' (n+m) (Word.combine n m xL xH, Word.combine n m yL yH).
  Proof. 
    unfold dv_adder' in *.   
    set (gsL := Word.carry_add n xL yL false) in *. 
    set (gsH := Word.carry_add m xH yH false) in *. 
    set (ptL := Word.carry_add n xL yL true) in *. 
    set (ptH := Word.carry_add m  xH yH true) in *. 
    rewrite (surjective_pairing gsL) in *. 
    rewrite (surjective_pairing gsH) in *. 
    rewrite (surjective_pairing ptL) in *. 
    rewrite (surjective_pairing ptH) in *. 
    intros. 
    Lemma tt A B (x :A) (y : B) x' y' : (x, y) = (x',y') -> x = x' /\ y = y'. 
      intros H; injection H. intuition.
    Qed.
    unfold PG' , Fix'' in *. 
    repeat match goal with 
             H : (_,_) = (_,_) |- _ => apply tt in H; destruct H as [? ?]
           end; subst. 
    set (x := Word.combine n m xL xH).
    set (y := Word.combine n m yL yH).
    
    set (gs:= Word.carry_add (n + m) x y false) in *. 
    set (pt:= Word.carry_add  (n + m) x y true) in *. 
    rewrite (surjective_pairing gs).
    rewrite (surjective_pairing pt).
    
    repeat f_equal.
    unfold gsL ,gsH, ptL, ptH, gs, pt, x , y. 
    rewrite Word.overflow_combine. 
    reflexivity. 
    
    unfold gsL ,gsH, ptL, ptH, gs, pt, x , y. 
    rewrite Word.overflow_combine. 
    reflexivity. 
    
    unfold gsL ,gsH, ptL, ptH, gs, pt, x , y. 
    rewrite Word.add_add'. 
    unfold Word.add'.
    destruct (Word.carry_add n xL yL false ).
    destruct b. 
    destruct ( Word.carry_add m xH yH true). reflexivity. 
    destruct (Word.carry_add m xH yH false); reflexivity. 
    
    unfold gsL ,gsH, ptL, ptH, gs, pt, x , y. 
    rewrite Word.add_add'. 
    unfold Word.add'.
    destruct (Word.carry_add n xL yL true ).
    destruct b. 
    destruct ( Word.carry_add m xH yH true). reflexivity. 
    destruct (Word.carry_add m xH yH false); reflexivity. 
  Qed.

    
  Lemma Implement_dv_adder n : forall x y s t G P, Implement (dv_adder n x y s t G P )
    (Iso_Phi _ [2^n] & Iso_Phi _ [2^n])%reif
    (Iso_tag bool _ & Iso_tag  bool _ & Iso_Phi _ [2^n] & Iso_Phi _ [2^n])%reif
    (dv_adder' [2^n]).
  Proof. 
    induction n; intros. 
    unfold dv_adder. 
    intros ins outs H.
    assert (H' := Implement_base_adder x y s t G P ins outs H).
    apply H'. 
    
    red. intros ins outs H. 
    simpl dv_adder in H. 
    rinvert. 

    unfold plug_final in Hk0. apply  RewireE_Implement in Hk0. 
    apply (ONE_Implement (Iso_Phi _ _)%reif) in Hk4. 
    apply (ONE_Implement (Iso_Phi _ _)%reif) in Hk7. 
    unfold combines in Hk5. rinvert. realise_all. 
    apply Implement_combine in Hk9. 
    apply Implement_combine in Hk10. 
    apply Implement_Fix in Hk6. 
    apply IHn in Hk3; apply IHn in Hk8; clear IHn.
    apply Implement_high_lows in Hk. 
    unfold id in *. 
    simpl pow2 in *. 
    unreify_all bool. 
    
    repeat 
      match goal with 
        x : _ -> bool |- _ => unreify x
        |  x : _ -> bool |- 
          context [@reify _ _ ?R ?y] =>
          constr_eq x y;
          match goal with 
            |- context [@reify _ _ ?Q x] =>
              let H := fresh in
                assert (H : @reify _ _  R x = @reify _ _ Q x) by reflexivity;
                  rewrite H; clear H
          end
      end.
    destruct_all.
    intros H; injection H. repeat intros. unfold fst, snd in *.  subst. 
    injection Hk. clear Hk; intros. subst. 
    injection Hk5. clear Hk5. intros; subst. 
    clear H. 
    injection Hk2; clear Hk2; intros; subst. 
    clear - Hk1 Hk6 Hk3 Hk8.  
    rename w into x.
    rename w0 into y.
    set (xL := Word.low [2^n] [2^n] x) in *. 
    set (yL := Word.low [2^n] [2^n] y) in *. 
    set (xH := Word.high [2^n] [2^n] x) in *. 
    set (yH := Word.high [2^n] [2^n] y) in *.
    
    
    rewrite (Word.combine_low_high [2^n] [2^n] x) . 
    rewrite (Word.combine_low_high [2^n] [2^n] y) . 
    
    eapply dv_adder_invar; eassumption. 
  Qed.
End ADD. 
  