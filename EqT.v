(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Bool Common.
Require EqNat.

(** eq-types : types with a boolean equality  *)
Class eqT (A : Type) : Type := {
    equal : A -> A -> bool ;
    _eqr  : forall x y, reflect (x = y) (equal x y)
}.

Section eqT.
    Context `{eqT}.
    Lemma eqT_true x y : equal x y = true -> x = y.
    Proof. destruct H as [eq H']; simpl.
        specialize  (H' x y).
        revert H'; case (eq x y); intros H';
        inversion H'; auto.
        discriminate.
    Qed.

    Lemma eqT_false x y : equal x y = false -> x <> y.
    Proof. destruct H as [eq H']; simpl.
        specialize  (H' x y).
        revert H'; case (eq x y); intros H';
        inversion H'; auto.
        discriminate.
    Qed.
End eqT.

Instance eqT_zero : eqT zero :=
    {| equal := fun _ _ => true  |}.
    Proof.
        abstract tauto.
    Defined.

Instance eqT_unit : eqT unit :=
    {|equal := fun _ _ => true |}.
    Proof.
        abstract (intros [] [] ; constructor; reflexivity).
    Defined.

Instance eqT_tag {t}: eqT (tag t) :=
    {|equal := fun _ _ => true |}.
    Proof.
        abstract (intros [] [] ; constructor; reflexivity).
    Defined.

Instance eqT_bool : eqT bool :=
    {| equal := Bool.eqb |}.
    Proof.
        abstract (intros [|] [|]; constructor; firstorder).
    Defined.


Instance eqT_nat : eqT nat :=
    {| equal := EqNat.beq_nat |}.
    Proof.
        abstract
        (
            intros;
            case_eq (EqNat.beq_nat x y); constructor;
            [apply EqNat.beq_nat_true | apply EqNat.beq_nat_false];
            auto
        ).
    Defined.

Section eqT_sum.
    Context {A} {B} {DA : eqT A} {DB : eqT B}.

    Definition eq_sum (x y: A + B) :=
        match x,y with
        | inl a, inl b => equal a b
        | inr a, inr b => equal a b
        | _, _         => false
        end.

    Lemma eq_sum_reflect : forall x y : A + B, reflect (x = y) (eq_sum x y).
    Proof.
        intros [x|x] [y|y]; simpl.
        case_eq (equal x y); constructor.
        apply eqT_true in H. rewrite H. reflexivity.
        apply eqT_false in H. intros H'; injection H'; tauto.
        constructor. discriminate.
        constructor. discriminate.
        case_eq (equal x y); constructor.
        apply eqT_true in H. rewrite H. reflexivity.
        apply eqT_false in H. intros H'; injection H'; tauto.
    Qed.

    Global Instance eqT_sum : eqT (A + B) := {|
        equal := eq_sum;
        _eqr := eq_sum_reflect
    |}.
End eqT_sum.

Section eqT_sum'.
    Variable A B : Type.
    Variable X : eqT  (A + B).

    Instance  eqT_left : eqT A :=
        {| equal := fun x y => equal (inl  x) (inl  y) |}.
    Proof.
        intros.
        case _eqr; constructor.
        injection e; tauto.
        intros H; subst; tauto.
    Qed.

    Instance  eqT_right : eqT B :=
        {| equal := fun x y => equal (inr x) (inr  y) |}.
    Proof.
        intros.
        case _eqr; constructor.
        injection e; tauto.
        intros H; subst; tauto.
    Qed.
End eqT_sum'.

Instance eqT_prod (A B : Type) (ea : eqT A) (eb : eqT B) : eqT (A * B) :=
    Build_eqT _
        (fun x y =>
            andb (equal (fst x) (fst y)) (equal (snd x) (snd y))
        ) _.
    Proof.
        intros [x1 x2] [y1 y2]; do 2 case _eqr; simpl; constructor; congruence.
    Defined.

