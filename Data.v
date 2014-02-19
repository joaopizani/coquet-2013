(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

Require Import Axioms.

(* One need to unfold these combinators in the proofs *)
Section wrap.
    Context {A : Type}.

    Definition select_left {n} {m} (x : (n + m) -> A) : n -> A := fun e => (x (inl _ e)).

    Definition select_right {n} {m} (x : (n + m) -> A) : m -> A := fun e => (x (inr _ e)).

    Definition lift {n} {m} (f : m -> n) (x : n -> A) : m -> A := fun e => x (f e).

    Definition app {n m} (x : n -> A) (y : m -> A) : n + m -> A :=
        fun e => match e with inl e => x e | inr e => y e end.

    Lemma expand {n m} (x : n + m -> A) : x = app (select_left x) (select_right x).
    Proof.
        apply functional_extensionality.
        intros [e|e]; reflexivity.
    Qed.

    Lemma left_app {n m} (x : n -> A) (y : m -> A) : select_left (app x y) = x.
    Proof.
        apply functional_extensionality.
        intros e; reflexivity.
    Qed.

    Lemma right_app {n m} (x : n -> A) (y : m -> A) : select_right (app x y) = y.
    Proof.
        apply functional_extensionality.
        intros e; reflexivity.
    Qed.

    Lemma app_projections {n m} x y (z : n + m -> A) (H : app x y = z) :
        x = select_left z /\ y = select_right z.
    Proof.
        rewrite <- H. rewrite left_app. rewrite right_app. tauto.
    Qed.
End wrap.


Require Import Common.

Lemma time_left : forall A n m (v : n + m -> stream A) t,
    time (select_left v) t = select_left (time v t).
Proof.
    intros; compute; apply functional_extensionality; reflexivity.
Qed.

Lemma time_right : forall A n m (v : n + m -> stream A) t,
    time (select_right v) t = select_right (time v t).
Proof.
    intros; compute; apply functional_extensionality; reflexivity.
Qed.

Lemma time_lift : forall A n m (v : n  -> stream A) (f : m -> n) t,
    time (lift f v) t = lift f (time v t).
Proof.
    intros; compute; apply functional_extensionality; reflexivity.
Qed.

