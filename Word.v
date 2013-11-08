(**************************************************************************)
(*  Copyright 2010 2011, Thomas Braibant                                  *)
(*                                                                        *)
(**************************************************************************)

(** n-bit integers, represented using Coq binary integers.  Mainly
   adapted from X. Leroy Machine Integers lib, to the dependent
   setting *)

Require Import Vector. 
Require Import ZArith.
Require Bool. 

Notation "[2^ p ]" := (two_power_nat p).
Lemma two_power_nat_0 : ([2^0] = 1)%Z.
Proof.  
  reflexivity. 
Qed.
  
Open Scope Z_scope.

Definition zlt x y := match x ?= y with Lt => true | _ => false end. 
Lemma zlt_lt x y: Bool.reflect (x < y) (zlt x y).
Proof. 
  unfold zlt. 
  assert( H:= Zcompare_spec x y).
  revert H. 
  case_eq (x ?= y); intros H Hs; constructor; inversion_clear Hs.
  subst.  apply Zlt_irrefl. 
  auto.
  auto with zarith.
Qed.
Instance Zle_Refl : Reflexive Zle. Proof. intros x; apply Zle_refl. Qed.
Instance Zle_Trans : Transitive Zle. Proof. intros x; apply Zle_trans. Qed.
Require Import Morphisms. 
Instance ZPlus_lt_compat_l_ : Proper (eq ==> Zlt ==> Zlt) Zplus. 
Proof.  repeat intro. subst. apply Zplus_lt_compat_l. auto. Qed.
Instance ZPlus_lt_compat_r_ : Proper (Zlt ==> eq ==> Zlt) Zplus. 
Proof.  repeat intro. subst. apply Zplus_lt_compat_r. auto. Qed.
Instance ZPlus_le_compat_l_ : Proper (eq ==> Zle ==> Zle) Zplus. 
Proof.  intros x x' H y y' H'. subst. apply Zplus_le_compat_l. auto. Qed.
Instance ZPlus_le_compat_r_ : Proper (Zle ==> eq ==> Zle) Zplus. 
Proof.   intros x x' H y y' H'. subst. apply Zplus_le_compat_r. auto. Qed.
Instance Zle_trans : Transitive Zle.  firstorder. Qed. 
Lemma Zle_refl' : forall x y, x = y -> x <= y. Proof. intros x y ->. apply Zle_refl. Qed. 

Lemma Zmod_plus_weak_l a b : (a + b) mod a = b mod a. 
Proof.
  replace (a + b) with (b + 1 * a) by ring. 
  apply Z_mod_plus_full. 
Qed.
Lemma Zmod_plus_weak_r a b : (b + a) mod a = b mod a. 
Proof.
  replace (b + a) with (b + 1 * a) by ring. 
  apply Z_mod_plus_full. 
Qed.

Lemma Zdiv_plus_weak : forall x y  n,  0 < n -> 0 <= y < n ->  (x * n + y) / n = x.
Proof. 
  intros. 
  rewrite Zplus_comm.
  rewrite Z_div_plus_full by omega.
  rewrite Zdiv_small by auto. 
  ring.
Qed.

Lemma add_pos : forall x y, 0 <= x -> 0 <= y -> 0 <= x + y.
Proof. intros; omega. Qed.

Lemma mult_pos : forall x y, 0 <= x -> 0 <= y -> 0 <= x * y.
Proof. 
  intros. replace (0) with (0*0). apply Zmult_le_compat; auto with arith; try reflexivity. ring.  
Qed.

Hint Resolve add_pos mult_pos : words. 

Record word n := mk_word
  {
    intval : Z;
    intrange : 0 <= intval < [2^ n]
  }.

Require Import EqT. 

Definition unsigned {n} (x: word n) : Z := intval n x.

Lemma unsigned_inj n (u v : word n) :  unsigned u = unsigned v -> u = v.
Proof.
  intros.  unfold unsigned in H.  
  destruct u as [u Hu]; destruct v as [v Hv]. 
  simpl in *. destruct H.
  Require Import ProofIrrelevance.
  rewrite (proof_irrelevance _ Hu Hv). 
  reflexivity.
Qed.

Definition equal n (x : word n) (y : word n) :=
  (match unsigned x ?= unsigned y with Eq => true | _ => false end) .

Instance eqT_word {n} : eqT (word n) := Build_eqT _  (equal n) _ . 
Proof. 
  intros. destruct x; destruct y. 
  unfold equal. simpl. 
  case_eq (intval0 ?= intval1); intros; simpl; constructor. 
  apply Zcompare_Eq_eq in H. 
  apply unsigned_inj. simpl; auto. 
  intros H'; injection H'; clear H'; intros H'. subst. rewrite Zcompare_refl in H. discriminate. 
  intros H'; injection H'; clear H'; intros H'. subst. rewrite Zcompare_refl in H. discriminate. 
Defined.

Definition signed {n} (x : word n) : Z :=
  if zlt (unsigned  x) [2^ (n - 1)]
  then unsigned  x
  else unsigned  x - [2^n ].

Lemma mod_in_range n:
  forall x, 0 <= Zmod x [2^ n] < [2^ n] .
Proof.
  intro.
  apply (Z_mod_lt x).
  reflexivity. 
Qed.

(** Conversely, [repr] takes a Coq integer and returns the corresponding
  machine integer.  The argument is treated modulo [modulus]. *)

Definition repr n (x: Z)  : word n := 
  mk_word n (Zmod x [2^ n]) (mod_in_range n x ).

Definition Z_shift_add (b: bool) (x: Z) :=
  if b then 2 * x + 1 else 2 * x.

Definition Z_of_bool : (bool) -> Z := fun f =>
  match f with 
    | true => 1%Z
    | false => 0%Z
  end.

Definition Z_bin_decomp (x: Z) : bool * Z :=
  match x with
  | Z0 => (false, 0)
  | Zpos p =>
      match p with
      | xI q => (true, Zpos q)
      | xO q => (false, Zpos q)
      | xH => (true, 0)
      end
  | Zneg p =>
      match p with
      | xI q => (true, Zneg q - 1)
      | xO q => (false, Zneg q)
      | xH => (true, -1)
      end
  end.

Fixpoint bits_of_Z (n: nat) (x: Z) {struct n}: vector bool n :=
  match n with
  | O => nil bool
  | S m =>
      let (b, y) := Z_bin_decomp x in
      let f := bits_of_Z m y in
        cons _ b f
  end.

Fixpoint Z_of_bits (n: nat)  {struct n}: vector bool n -> Z :=
  match n with
  | O => fun _ => 0
  | S m => fun f => 
    let (b,v) := uncons _ f in 
      Z_shift_add (b) (Z_of_bits m v)
  end.

Definition lt n (x y: word n) : bool :=
  zlt (unsigned x) (unsigned y).

Definition overflow n (x :Z)  : bool :=
  negb (zlt (x) [2^ n]).

Definition add n (x : word n) (y : word n) : word n:=
  repr n (unsigned x + unsigned y).
  
Definition incr n (x : word n) : word n :=  
  repr n (unsigned x + 1).

Definition high n m (x : word (n+m)) : word m :=
  repr m (unsigned x / [2^n]).

Definition low n m (x : word (n+m)) : word n :=
  repr n (unsigned x mod [2^n]).

Definition combine n m (low : word n) (high : word m)  : word (n+m) :=
  repr (n + m) ((unsigned high)*[2^n] + unsigned low).


Definition comb n xL xH := xH * [2^n] + xL. 

(* FIN des operations *)
Lemma two_power_nat_pos : forall n, [2^ n] > 0. 
Proof.  
  induction n; reflexivity.
Qed.
Lemma two_power_nat_plus : forall n m, 
  (two_power_nat (n + m) = two_power_nat n * two_power_nat m)%Z. 
Proof.
  intros. rewrite !two_power_nat_correct . 
  apply  Zpower_nat_is_exp. 
Qed.
Lemma two_power_nat_S :  forall n, [2^ S n] = [2^n] + [2^n].
Proof. 
  intros. change (S n) with (1 + n)%nat.
  rewrite  two_power_nat_plus.
  replace [2^1] with 2 by reflexivity. 
  ring. 
Qed.
Lemma two_power_nat_not_0 : forall n, [2^ n] <> 0.
Proof.
  induction n. compute. discriminate.
  rewrite two_power_nat_S. omega. 
Qed.
Lemma two_power_nat_lt_0 : forall n, 0 < [2^ n].
Proof.
  induction n. 
  replace [2^0] with 1 by reflexivity. omega. 
  rewrite two_power_nat_S. omega. 
Qed.
Lemma two_power_nat_le_0 : forall n, 0 <= [2^ n].
Proof.
  induction n. 
  replace [2^0] with 1 by reflexivity. omega. 
  rewrite two_power_nat_S. omega. 
Qed.
Lemma two_power_nat_pos' : forall n, [2^n] > 0. 
Proof. 
  intros. 
  assert (0 < [2^n]) by apply two_power_nat_lt_0. 
  auto with zarith. 
Qed.

Hint Resolve 
  two_power_nat_pos
  two_power_nat_S
  two_power_nat_not_0 
  two_power_nat_le_0 
  two_power_nat_pos'
  two_power_nat_lt_0: words. 

Definition check_overflow n x :=  (overflow n x,repr n x ).

Definition carry_add n (x y : word n) (b : bool): bool * word n :=
  check_overflow n (unsigned x + unsigned y + if b then 1 else 0).

Definition add' n m  (xL yL : word n)  (xH yH  : word m)cin :=
  let (middle, sumL) := carry_add n xL yL cin in 
  let (cout,sumH) := carry_add m xH yH middle in 
    (cout, combine n m  sumL sumH). 

Notation ZOB := Z_of_bool. 

Lemma Zmult_compat  (x x' y y' : Z) (H : x = x') (Hy : y = y'): 
  (x * y = x' * y')%Z.
Proof.     
  subst; reflexivity. 
Qed.

Lemma ZOB_compat : forall a b, a = b -> ZOB a = ZOB b. 
Proof. 
  intros [|] [|]; firstorder; discriminate. 
Qed.

(* preuves sur les nombres *)

Definition small n x := 0 <= x < [2^ n].
Definition big n x := exists k, x = [2^n] + k /\ small n k. 
Definition inrange n x := small n x \/ big n x. 

Lemma mod_small : forall n x, small n (x mod [2^n]).
Proof. 
  apply mod_in_range. 
Qed.
Hint Resolve mod_small : words.

Lemma unsigned_big : forall n x, unsigned (repr n x) = x mod [2^n].
Proof. reflexivity.  Qed.

Lemma unsigned_small : forall n x, small n x  -> unsigned (repr n x) = x.  
Proof. 
  intros.
  unfold unsigned. simpl.
  apply Zmod_small. auto. 
Qed.

Lemma unsigned_repr : forall n x, @unsigned n (repr n x) = x mod [2^n]. 
Proof. 
  reflexivity. 
Qed.

Lemma unsigned_is_small : forall n (x : word n), small n (unsigned x).
Proof. 
  intros. destruct x; auto. 
Qed.

Lemma unsigned_pos : forall n (x : word n), 0 <= unsigned x.
Proof. intros n [x H]; simpl; intuition. Qed.

Lemma  unsigned_pos' : forall n (x y : word n) ,
  0 <= unsigned x + unsigned y + 1. 
Proof. 
  intros. 
  assert (Hx := unsigned_is_small n x).
  assert (Hy := unsigned_is_small n y).
  unfold small in *. 
  omega. 
Qed.

Lemma unsigned_lt : forall n (x : word n), unsigned x < [2^n]. 
Proof. 
  intros. 
  assert (H := unsigned_is_small _ x). unfold small in *. 
  intuition. 
Qed.

Hint Resolve unsigned_lt unsigned_pos' unsigned_is_small unsigned_pos : words.

Lemma pos_is_small : forall x n, x < [2^n] -> 0 <= x -> small n x.
Proof. intros; unfold small;omega. Qed.

Lemma  lt_0_1 : 0 < 1. reflexivity. Qed.
Hint Resolve lt_0_1 : words.

Hint Resolve pos_is_small add_pos: words.

Lemma expand_big : forall n x, [2^n] <= x < [2^ S n] -> 
  x = x mod [2^n] + [2^ n].
Proof.
  intros. 
  rewrite( Z_div_mod_eq_full x [2^n]) at 1.
  replace (x / [2^ n]) with 1. 
  ring. 
  replace [2^ S n] with ([2^n] + [2^ n]) in H.
  assert (x / [2^n] < 2).
  apply        Zdiv_lt_upper_bound.        
  auto with words.  omega. 
  assert (1<= x / [2^n] ).
  apply        Zdiv_le_lower_bound.        auto with words. omega. 
  omega. auto with words. auto with words. 
Qed.
      
Lemma comb_lt n m low high : low < [2^n] -> high < [2^m] ->
  comb n low high < [2^m] * [2^n].
Proof. 
  unfold comb. 
  intros. 
  apply Zlt_le_trans with ( m := high  * [2^n] + [2^n]).
  apply Zplus_lt_compat_l. intuition. 
  transitivity (( high + 1 )* [2^n]) ; [apply Zle_refl'; ring|].
  assert (high + 1 <= [2^m]). omega. 
  apply Zmult_le_compat_r. auto. auto with words. 
Qed.    

Lemma comb_lt' n m low high : small n low -> small m high ->
  comb n low high < [2^m] * [2^n].
Proof. 
  unfold small. 
  intros; apply comb_lt; intuition.
Qed.    

Lemma comb_small n m low high : small n low  -> small m high -> 
  small (n+m) (comb n low high).
Proof. 
  unfold small. rewrite two_power_nat_plus.
  intros. 
  split. apply add_pos; intuition auto with words.
  unfold comb.
  rewrite (Zmult_comm [2^n] [2^m]). 
  apply comb_lt; intuition. 
Qed.

Lemma comb_plus : forall n x y x' y', comb n x y + comb n x' y' =
  comb n (x+x') (y+y').
Proof. 
  intros; unfold comb. ring. 
Qed.

Hint Resolve comb_small : words. 

Lemma unsigned_combine n m low high :
  unsigned (combine n m low high) = comb n (unsigned low) (unsigned high).
Proof.
  unfold combine, comb. 
  rewrite unsigned_small. reflexivity.
  apply comb_small; auto with words.  
Qed.

Lemma add_elim : forall n x y z, 0 <= x < [2^n] -> 0 <= y < [2^n] ->
  0 <= z <= 1 -> 
  (small n  (x + y + z) \/ big n (x+y+z)).
Proof. 
  intros. 
  destruct (Zle_or_lt [2^n] (x + y + z));
    [right| left; unfold small; now( auto with zarith)]. 
  exists ((x + y + z) mod [2^n]).
  split; [| auto with words].

  rewrite  (Z_div_mod_eq (x+y+z) [2^n]) at 1 by auto with words. 
  replace ((x+y+z )/ [2^n]) with 1; [ring|]. 
  assert (x+y+z < [2^n]*2 ) by omega. 
  assert ((x+y+z) /[2^n] < 2 ) by 
    (apply Zdiv_lt_upper_bound;  auto with zarith words). 
  apply Zle_antisym. 
  apply Zdiv_le_lower_bound; auto with words.  
  omega. 
  
Qed.

Lemma overflow_small n x : small n x -> overflow n x = false. 
Proof. 
  intros; unfold overflow. case zlt_lt; intros; try reflexivity.  
  unfold small in *;exfalso; omega. 
Qed.

Lemma overflow_big n x : big n x -> overflow n x = true. 
Proof. 
  unfold overflow, big, small. 
  intros H; destruct H. case zlt_lt. 
  intros; exfalso;omega. 
  reflexivity.
Qed.

Lemma comb_carry_small : forall n 
  low high  c, small n (low+c) -> comb n low high + c = comb n (low + c) high.
Proof. 
  intros. 
  unfold comb.
  ring. 
Qed. 

Lemma comb_carry_big : forall n low high c, big n (low + c) -> 
  comb n low high + c =  comb n  ((low+c) mod [2^n]) (high + 1).
Proof. 
  intros n low high c H. destruct H as [k [Hk Hk']].
  unfold comb. 
  transitivity (high*[2^n] + (low+c)); [ring|].
  rewrite Hk. 
  rewrite Zmod_plus_weak_l. 
  rewrite Zmod_small by apply Hk'. 
  ring. 
Qed.

  
  (* carry := if cin then 1 else 0 : Z *)
  (* low := unsigned xL + unsigned yL + carry : Z *)
  (* H : small n (unsigned xL + unsigned yL + carry) *)
  (* ============================ *)
  (*  comb n low (unsigned xH + unsigned yH) mod [2^n + m] = *)
  (*  comb n (low mod [2^n]) ((unsigned xH + unsigned yH) mod [2^m]) *)

Lemma comb_main n m low high:  
  small n low ->
  inrange m high ->
  comb n low high mod [2^n+m] =
  comb n (low mod [2^n]) (high mod [2^m]).
Proof.
  rewrite two_power_nat_plus.
  intros Hlow  [Hhigh | Hhigh];
  unfold comb;
  repeat  match goal with
    H : small ?n ?x |- context c [?x mod [2^?n]] =>
      rewrite (Zmod_small x [2^n]) by apply H
  end.

  Focus 1. 
  rewrite Zmod_small. reflexivity.
  unfold small in *.
  split. auto with words zarith.
  now (rewrite (Zmult_comm [2^n] _); apply comb_lt; intuition).
  
  Focus 1. 
  unfold comb. 
  destruct Hhigh as [k [Hk Hk']].
  rewrite Hk. 
  
  replace   (([2^m] + k) * [2^n] + low) with ( (k*[2^n] +low) +  ([2^n]*[2^m])) by ring.
  
  rewrite Zmod_plus_weak_l. 
  rewrite Zmod_plus_weak_r. 
  rewrite (Zmod_small k [2^m] Hk'). 
  rewrite Zmod_small. reflexivity.
  
  rewrite <- two_power_nat_plus.
  apply comb_small; auto. 
Qed.

Lemma inrange_plus : forall n x y, small n x -> small n y -> 
  inrange n (x + y).
Proof.
  intros. destruct (add_elim n x y 0); auto with words.
  split; simpl. reflexivity.  auto with zarith. 
  left. rewrite Zplus_0_r in H1.  auto. 
  right.  rewrite Zplus_0_r in H1.  auto. 
Qed.

Lemma inrange_plus' : forall n x y, small n x -> small n y -> 
    inrange n (x + y +1).
Proof.
  intros. destruct (add_elim n x y 1); auto with words.
  split; simpl; auto with zarith. 
  left. auto. 
  right; auto. 
Qed.

Hint Resolve inrange_plus inrange_plus' : words. 

(** oveflow does not care of the small part, it it is small *)
Lemma overflow_comb_small n m low high (H : small n low ) (Hx : 0 <= high): 
    overflow (n +m )(comb n low high) = overflow (n+m) (comb n 0 high).
Proof. 
  unfold overflow. 
  unfold comb. 
  rewrite two_power_nat_plus.     
  repeat case zlt_lt; intros; try reflexivity; exfalso. 
  unfold small in H. omega. 
  rewrite Zplus_0_r in z. 
  rewrite (Zmult_comm [2^n]) in z.
  apply Zmult_lt_reg_r in z; auto with words. 
  assert (Hx' : 0 <= low < [2^n]). auto with words. 
  assert ( HH := comb_lt' n m low high  ).
  unfold small in *.  intuition. unfold comb in *.
  apply n0. rewrite (Zmult_comm [2^n]). auto.
Qed.

(** the overflow of the combination is the overflow of the high part
if the low part is nul *)

Lemma overflow_comb : forall 
  n m x, 0 <= x -> overflow (n+m) (comb n 0 x) = overflow m x. 
Proof.
  intros; unfold overflow.  unfold comb.
  rewrite two_power_nat_plus. repeat case zlt_lt; intros; try reflexivity.   
  exfalso. apply n0. 
  rewrite Zplus_0_r in z. 
  rewrite (Zmult_comm [2^n]) in z.
  apply Zmult_lt_reg_r in z; auto with words. 
  exfalso. apply n0.
  rewrite Zplus_0_r.
  rewrite (Zmult_comm [2^n]) .
  apply Zmult_lt_compat_r; auto with words. 
Qed.

(** Adding combined numbers is the same as adding them separately, and
merging the resultt*)

Lemma add_add' n m (xH yH: word m) (xL yL : word n) cin: 
  carry_add (n + m) (combine n m xL xH)(combine n m yL yH) cin =
  add' n m xL yL xH yH cin.
Proof. 
  unfold add'.
  unfold carry_add. 
  unfold check_overflow. 
  apply injective_projections;
  unfold fst, snd;
    [| apply unsigned_inj].
  

  Focus 2. 
  rewrite ! unsigned_repr.
  rewrite ! unsigned_combine.
  rewrite ! unsigned_repr.

  set (carry := if cin then 1 else 0).
  rewrite comb_plus. 
  set (low := unsigned xL + unsigned yL + carry).
  
  destruct (add_elim n (unsigned xL) (unsigned yL) carry ); auto with words. 
  destruct cin; simpl in *;  subst carry; auto with zarith. 
  rewrite overflow_small; auto with words.

  rewrite comb_carry_small; auto. 
  fold low. 
  rewrite  Zplus_0_r. 
  rewrite comb_main by auto with words. reflexivity.

  rewrite (overflow_big ) by auto. 
  rewrite comb_carry_big by auto. fold low.
  rewrite comb_main by auto with words.  
  rewrite Zmod_mod. reflexivity. 

  (* Second. *)
  Focus 1.
  rewrite ! unsigned_combine.
  set (carry := if cin then 1 else 0).
  rewrite comb_plus. 
  set (low := unsigned xL + unsigned yL + carry).

  destruct (add_elim  n (unsigned xL) (unsigned yL) carry ); auto with words. 
  destruct cin; simpl in *;  subst carry; auto with zarith. 
  rewrite (overflow_small n low) by auto with words.
  rewrite comb_carry_small by auto with words. 

  
  rewrite  overflow_comb_small by  auto with words. 
  rewrite Zplus_0_r. 
  apply overflow_comb; auto with words.
  rewrite comb_carry_big by  auto with words. fold low.
  rewrite  overflow_comb_small by auto with words. 
  rewrite (overflow_big n low) by apply H. 
  apply overflow_comb; auto with words. 
Qed.

Lemma overflow_combine n m xL xH yL yH cin : 
  fst (carry_add (n+m) (combine n m xL xH ) (combine n m yL yH) cin)=
  (fst (carry_add m xH yH false) || 
    (fst (carry_add m xH yH true) && fst (carry_add n xL yL cin)))%bool.
Proof. 
  rewrite add_add'. 
  unfold add'. 
  case_eq (carry_add n xL yL cin). intros b w Hbw. 
  case_eq (carry_add m xH yH b). intros b' w' Hbw'.
  unfold fst. 
  unfold carry_add in *. 
  unfold check_overflow in *. 
  injection Hbw; clear Hbw; intros _ Hbw . 
  injection Hbw'; clear Hbw'; intros _ Hbw' . 
  destruct b. 
  rewrite Bool.andb_true_r.  rewrite Hbw'. 
  
  Lemma overflow_carry_true n x y:  
    0 <= x ->
    0 <= y -> 
    overflow n (x + y + 0) = true ->
    overflow n (x + y + 1) = true.
    unfold overflow. 
    do 2 case zlt_lt; try reflexivity; intros;exfalso.  discriminate. 
     omega.
   Qed.
   case_eq (overflow m (unsigned xH + unsigned yH + 0)); intros. 
   apply overflow_carry_true in H. rewrite H in Hbw'.  subst. reflexivity. 
   auto with words. 
   auto with words. 
   simpl; reflexivity. 
   rewrite Bool.andb_false_r. 
   rewrite Bool.orb_false_r. 
   symmetry; apply Hbw'. 
 Qed.

(* Compositions  *)
Lemma Z_bin_decomp_Z_shift_add b x : 
  Z_bin_decomp (Z_shift_add b x) = (b,x).
Proof.  
  intros. unfold Z_shift_add. destruct b; destruct x; simpl; auto.
  destruct p; simpl; auto. f_equal. f_equal.
  rewrite <- Pplus_one_succ_r. apply Psucc_o_double_minus_one_eq_xO.
Qed.

Lemma Z_shift_add_bin_decomp:
  forall x,
    Z_shift_add (fst (Z_bin_decomp x)) (snd (Z_bin_decomp x)) = x.
Proof.
  destruct x; simpl.
  auto.
  destruct p; reflexivity.
  destruct p; try reflexivity. simpl.
  assert (forall z, 2 * (z + 1) - 1 = 2 * z + 1). intro; omega.
  generalize (H (Zpos p)); simpl. congruence.
Qed.

Lemma Z_of_bits_compose:
  forall  m n f ,
    Z_of_bits (n + m) f =
     Z_of_bits m (skipn _ _ f) * two_power_nat n
   + Z_of_bits n (firstn _ _ f) .
Proof.
  induction n; intros.
  simpl.  rewrite two_power_nat_0.  ring.

  simpl in f. destruct f. 
  simpl. rewrite IHn. unfold Z_shift_add. case b.  
  rewrite two_power_nat_S. ring. 
  rewrite two_power_nat_S. ring. 
Qed.

Lemma Z_of_bits_of_Z n : forall x ( H : 0 <= x < [2^n]),
  Z_of_bits n ( bits_of_Z n x ) = x.
Proof.
  induction n; simpl.
  intros. rewrite two_power_nat_0 in H. omega.
  intros.
  case_eq ( Z_bin_decomp x). 
  intros b z Hbz.  simpl. rewrite IHn. 
  clear - Hbz. rewrite (surjective_pairing (Z_bin_decomp x)) in Hbz.
  injection Hbz. clear Hbz. intros <- <-. apply Z_shift_add_bin_decomp.

  intros. rewrite (surjective_pairing (Z_bin_decomp x)) in Hbz.
  injection Hbz. clear Hbz. intros <- _. 

  rewrite <- (Z_shift_add_bin_decomp x) in H.
  unfold Z_shift_add in H. destruct (fst (Z_bin_decomp x));  rewrite two_power_nat_S in H; omega.
Qed.

Lemma bits_of_Z_of_bits n : forall x ,
   bits_of_Z n (Z_of_bits n  x ) = x.
Proof.
  induction n; simpl.
  intros [];reflexivity. 
  intros [b z]. simpl. 
  rewrite Z_bin_decomp_Z_shift_add. 
  rewrite IHn. 
  reflexivity. 
Qed.  

Definition wordify n (x : vector (bool) n) :word n :=
  repr n(Z_of_bits n  x) .

Definition word_of_bool n (b : bool) : word n :=
  repr n (if b then 1 else 0).

Definition vecify n (v : word n) : vector bool n :=
  bits_of_Z n (intval n v).

Lemma wordify_vecify_id n x: wordify n (vecify n x) = x. 
Proof.
  unfold wordify, vecify. 
  rewrite Z_of_bits_of_Z.
  apply unsigned_inj. simpl. rewrite Zmod_small. reflexivity. 
  apply x. 
  apply x. 
Qed. 

Lemma Z_of_bits_small : forall n x, small n (Z_of_bits n x). 
Proof. 
  induction n; simpl; unfold small in *.
  intros. rewrite two_power_nat_0. omega. 
  intros [b v]. simpl. 
  specialize (IHn v). unfold Z_shift_add. 
  rewrite two_power_nat_S.
  destruct b; omega.
Qed. 

Hint Resolve Z_of_bits_small : words. 

Lemma vecify_wordify_id n x: vecify n (wordify n x) = x. 
Proof. 
  intros. unfold wordify, vecify.
  rewrite unsigned_small.
  apply bits_of_Z_of_bits. 
  apply Z_of_bits_small. 
Qed.

Lemma high_wordify : forall n p x,
  high n p (wordify (n+p) x) = wordify p (Vector.skipn n p x).
Proof. 
  intros. 
  unfold wordify. 
  rewrite Z_of_bits_compose. 
  unfold high. 
  rewrite unsigned_small by 
    (apply comb_small; auto with words).
  f_equal.
  apply Zdiv_plus_weak. 
  auto with words. 
  apply Z_of_bits_small. 
Qed.

Lemma low_wordify : forall n p x,
  low n p (wordify (n+p) x) = wordify n (Vector.firstn n p x).
Proof. 
  intros. 
  unfold wordify.
  rewrite Z_of_bits_compose. 
  unfold low. 
  rewrite unsigned_small by 
    (apply comb_small; auto with words).
  f_equal.
  rewrite Zplus_comm. rewrite Z_mod_plus_full.
  apply Zmod_small. 
  apply Z_of_bits_small. 
Qed.

Lemma combine_low_high : forall n m (x : word (n+m)), 
  x = combine n m (low n m x)(high n m x).
Proof.
  unfold combine, low, high. 
  intros. 
  rewrite !unsigned_small.
  apply unsigned_inj. 
  rewrite Zmult_comm. 
  rewrite <- Z_div_mod_eq.
  rewrite unsigned_small by auto with words. 
  reflexivity. 
  auto with words. 
  auto with words.
  assert (small (n+m)(unsigned x) ) by auto with words. 
  unfold small in *. 
  rewrite two_power_nat_plus in H. 
  split.
  apply Z_div_pos; intuition.
  apply Zdiv_lt_upper_bound; intuition.
  rewrite Zmult_comm. auto. 
Qed.

Lemma wordify_combine : forall n p x y, 
  wordify (n + p)(append n p x y)=combine n p (wordify _ x) (wordify  _ y).
Proof.
  unfold wordify. 
  intros. 
  rewrite Z_of_bits_compose.
  replace (skipn n p (append n p x y)) with y. 
  replace (firstn n p (append n p x y)) with x. 
  unfold combine. 
  rewrite 2 unsigned_small by auto with words. 
  reflexivity. 
  
  induction n. simpl. destruct x; reflexivity. 
  simpl. simpl in x. destruct x. f_equal. apply IHn. 


  induction n. simpl. destruct x; reflexivity. 
  simpl. simpl in x. destruct x. f_equal. apply IHn. 

Qed. 

Lemma unsigned_zero : forall x : word 0, unsigned x = 0%Z. 
Proof. 
  intros; destruct x. simpl.  rewrite two_power_nat_0 in *. omega. 
Qed. 

Lemma eq_zero : forall (x y: word 0), x = y. 
Proof. 
  intros. 
  apply unsigned_inj. 
  rewrite 2 unsigned_zero. 
  reflexivity. 
Qed.       
  