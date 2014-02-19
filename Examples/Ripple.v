(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Add LoadPath "../".
Require Import Data EqT Common Finite Reify Base  ZArith String.
Require Import Sumn Vector.

Definition add n a b c := let (c,s) := Word.carry_add n a b c in (s,c).

Module Type T.
  Parameter tech : Techno.
  Parameter tech_spec_bool : Technology_spec tech bool.


  Parameter FADD: forall a b cin sum cout,
  @circuit tech
  ([:cin] + ( [:a]  + [:b] ))
  ([:sum]  + [:cout]).

  Hypothesis  FADD_Implement : forall a b cin sum cout,
    @Implement tech bool tech_spec_bool _ _
    (FADD a b cin sum cout) _ _
    _
    _
    (fun x =>
      match x with (carry,(a,b)) =>
        (xorb a (xorb b carry),
          ( a && b) || carry && (xorb a b)
        )%bool
      end
    ).
End T.


Module ADD (X : T).
  Import X.
  Existing Instance tech.
  Existing Instance tech_spec_bool.

  Notation I x p := (Iso_Phi x p).

  Definition high_low x n p :
    circuit
    (sumn [:x] (n + p))
    (sumn [:x] n + sumn [:x] p)
    :=
    Plug     ((sumn_add _ n p)).

  Lemma Implement_high_low x n p:
    Implement (high_low x n p)
    (I _ (n + p) )%reif
    ((I _ n & I _ p))%reif
    (fun x => (Word.low n p x, Word.high n p x)).
  Proof.
    intros ins outs H.
    apply inversion_Plug in H.
    rewrite H.

    unfold reify.
    unfold reify_.

    rewrite Reify.iso_prod.
    f_equal; simpl.

    rewrite Word.low_wordify;
    f_equal; rewrite first_iso_sumn; reflexivity.

    rewrite Word.high_wordify;
    f_equal; rewrite skipn_iso_sumn; reflexivity.
  Qed.

  Definition combine' x n p :
    circuit
    (sumn [:x] n + sumn [:x] p)
    (sumn [:x] (n + p))
    :=
    Plug     ((sumn_add' _ n p)).

  Lemma Implement_combine' x n p:
    Implement (combine' x n p)
    ((I _ n & I _ p))%reif
    (I _ (n + p) )%reif
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


  Program Definition high_lows x y n p :
    circuit
    (sumn [:x] (n + p) + sumn [:y] (n+p))
    (sumn [:x] n + sumn [:y] n + (sumn [:x] p + sumn [:y] p)) :=
    (high_low x n p & high_low y n p)
    |>
    RewireE
    ((I x n & I x p) & (I y n & I y p))%reif
    ((I x n & I y n) & (I x p & I y p))%reif
    _
    (fun x =>
      let xLH := fst x in
      let yLH := snd x in
        ((fst xLH, fst yLH),       (snd xLH, snd yLH))
    )
    _ .
  Next Obligation.
    revert X; plug_def.
  Defined.
  Next Obligation.
    plug_auto.
  Qed.

  Lemma Implement_high_lows x y n p : Implement (high_lows x y n p)
    (I x (n + p) & I y (n + p))%reif
    ((I x n & I y n) & (I x p & I y p))%reif
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

  Definition v1 x : vector bool 1:= Vector.cons  _ x (Vector.nil bool).

  (* In order to make the following circuit "simpler", we package FADD *)

  Program Definition FADD' a b cin s cout :
    circuit ([:cin] + sumn [:a] 1 + sumn [:b] 1) (sumn [:s] 1 + [:cout]) :=
    RewireE
    ([b: _ ]& ([b:_] & [!]) & ( [b: _ ] & [!]))%reif
    ([b: _] & ([b: _] & [b: _ ]))%reif
    _
    ( fun x : bool * Vector.vector bool 1 * Vector.vector bool 1 =>
      match x return _ with
        | (c,(x, _),(y, _)) => (c,(x,y))
      end
    ) _
    |> FADD a b cin s cout
    |> RewireE
      ([b:s] & [b:_])%reif
      (Iso_Phi _ 1 & [b:cout])%reif
      _
      (fun x : bool * bool  => (Word.wordify 1 (v1 (fst x)), snd x))
      _.
  Next Obligation.
    revert H; plug_def.
  Defined.
  Next Obligation.
    plug_auto.
  Defined.
  Next Obligation.
    revert H; plug_def. destruct H.
  Defined.
  Next Obligation.
    plug_auto.
  Defined.


  Lemma FADD_2 cin a b cout s : Implement (FADD' a b cin s cout)
    ([b:_] & Iso_Phi _ 1 & Iso_Phi _ 1)%reif
    (Iso_Phi _ 1 & [b:_ ])%reif
    (fun x => match x with (c,a,b) => add 1 a b c end).
  Proof.
    intros ins outs H.
    unfold FADD' in H.
    rinvert. apply FADD_Implement in Hk1.
    realise_all.
    unreify_all bool. intros_all.
    Definition Iso_w2 : Iso (bool * Word.word 1 * Word.word 1) (bool * (bool * unit) * (bool * unit)).
    apply Iso_prod. 2: apply (Iso_sym  (Iso_word 1)).
    apply Iso_prod. 2: apply (Iso_sym  (Iso_word 1)).
    constructor; apply id.
    Defined.


    cast ins (Iso_sym Iso_w2);[|reflexivity].
    unreify_all bool.
    destruct_all; simpl; clear.
    apply eqT_true. boolean_eq.
  Qed.


  Program Fixpoint RIPPLE cin a b cout s n :
    circuit ([:cin] + sumn [:a] n + sumn [:b] n) (sumn [:s] n + [:cout]) :=
    match n with
      | O => RewireE ([b:cin] & Iso_Phi _ 0 & Iso_Phi _ 0 )%reif (Iso_Phi _ 0 & [b:cout])%reif _
        (fun x =>
          match x return _ with
            | (c,x,y) => (x,c)
          end
        ) _
      | S p =>
        RewireE
        ([b:cin] & Iso_Phi a (S p) & Iso_Phi b (S p))%reif
        ([b:cin] & (Iso_Phi a (S p) & Iso_Phi b (S p)))%reif
        (sum_assoc)
        (fun x => match x : bool * Word.word (S p) * Word.word (S p) return _ with |(a,b,c) => (a,(b,c)) end )
        _
        |>
        (ONE [:cin] & high_lows a b 1 p)
        |> RewireE
          ([b:cin] & ((Iso_Phi a 1 & Iso_Phi b 1) & (Iso_Phi a p & Iso_Phi b p)))%reif
          ([b:cin] & Iso_Phi a 1 & Iso_Phi b 1 & (Iso_Phi a p & Iso_Phi b p))%reif

          _
          (fun x => match x return _ with
                     | (c,((a1,b1),(ap,bp))) => (c,a1,b1,(ap,bp))
                   end
          )
          _
        |> (FADD' a b cin s "mid" & ONE (sumn [:a] p + sumn [:b] p))
        |> RewireE
          (Iso_Phi s 1 & [b:"mid"] & (Iso_Phi a p & Iso_Phi b p ))%reif
          (Iso_Phi s 1 & ([b:"mid"] &Iso_Phi a p & Iso_Phi b p ))%reif
          _
          (fun x => match x return _ with
                     |(s,c,(a,b)) => (s,(c,a,b))
                   end
          )
          _
        |> (ONE (sumn [:s] 1) & RIPPLE ("mid")%string a b cout s p)
        |>  RewireE
          (Iso_Phi s 1 & (Iso_Phi s p & [b:cout]))%reif
          (Iso_Phi s 1 & Iso_Phi s p & [b:cout])%reif
          sum_assoc'
          (fun x => match x return _ with
                     | (s1,(s2,c)) => (s1,s2,c)
                   end
          ) _
        |> combine' s 1 p & ONE [:cout]
    end.
  Next Obligation.
    revert H; intros [[]| H]; repeat left; constructor.
  Defined.
  Next Obligation.
    abstract plug_auto.
  Defined.
  Next Obligation.
    abstract plug_auto.
  Defined.
  Next Obligation.
    revert X; plug_def.
  Defined.
  Next Obligation.
    abstract plug_auto.
  Defined.
  Next Obligation.
    revert X; plug_def.
  Defined.
  Next Obligation.
    abstract plug_auto.
  Defined.
  Next Obligation.
    abstract plug_auto.
  Defined.

  Lemma Implement_adder n cin a b  cout s : Implement (RIPPLE cin a b cout s n)
    ([b:_] & Iso_Phi _ n & Iso_Phi _ n)%reif
    (Iso_Phi _ n & [b:_ ])%reif
    (fun x => match x with (x,a,b) => add n a b x end).
  Proof.
    revert cin cout .
    induction n.
    intros cin cout ins outs H. unfold  RIPPLE in H.
    realise_all.
    rewrite H. clear.  unreify_all bool.
    destruct_all.
    apply eqT_true.
    rewrite( Word.eq_zero w (Word.repr 0 1)).
    rewrite( Word.eq_zero w0 (Word.repr 0 0)).
    destruct b0; reflexivity.

    (* recursive case *)
    intros cin cout ins outs H.
    simpl in H.
    rinvert.
    apply IHn in Hk8.
    apply FADD_2 in Hk4.
    apply (ONE_Implement (I _ _ & I _ _)%reif) in Hk9.
    apply (ONE_Implement (I _ 1)%reif) in Hk2.
    apply (ONE_Implement ([b:_])%reif) in Hk7.
    apply (ONE_Implement ([b:_])%reif) in Hk6.
    clear IHn.
    apply (Implement_combine' s 1 n) in Hk0.
    apply (Implement_high_lows a b 1  n) in Hk10.
    realise_all.

    simpl in outs.
    unreify_all bool.

    destruct_all.
    unfold fst, snd.
    intros_all.
    unfold id.
    change (S n) with (1+n).
    symmetry.
    rewrite( Word.combine_low_high 1 n w) at 1.
    rewrite( Word.combine_low_high 1 n w0) at 1.
    unfold add.
    rewrite Word.add_add'. unfold Word.add'. reflexivity.
  Qed.
End ADD.

