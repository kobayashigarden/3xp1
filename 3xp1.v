(*

Please use this URL when linking to this file.
https://figshare.com/account/home#/collections/6472138

This proof file runs on Coq 8.16.
  https://coq.inria.fr/

### This is a complete formal proof of the Collatz conjecture, a well-known unsolved problem in mathematics.

  All theory and all implementation of this proof was developed entirely by Teruyuki and Yoko Kobayashi.
  This project began in May 2022 and was completed in March 2023.

  We have not been able to obtain the cooperation of any academic institution and therefore lack the funds.
  We need R&D funds. Please help us.

  Copyright Teruyuki and Yoko Kobayashi.
    https://orcid.org/0000-0002-5662-6948
    https://orcid.org/0000-0002-2704-3882

*)

Require Import Arith Lia Unicode.Utf8.

Section Utility_Lemma.

Lemma odd_false_even : ∀ x : nat, 
  Nat.odd x = false → Nat.Even x.
Proof.
  intros x H. unfold Nat.odd in H.
  induction x as [|x' IHx'].
  - apply Nat.even_spec.
    apply Nat.even_0.
  - rewrite Nat.even_succ in H.
    apply Bool.negb_false_iff in H.
    apply Nat.even_spec.
    rewrite Nat.even_succ; auto.
Qed.

Lemma mod_unique_rev: ∀ (a b r : nat),
  r < b → r = a mod b →
  exists q, a = b * q + r.
Proof.
  intros a b r Hq Hmod.
  exists (a / b).
  assert (a = b * (a / b) + (a mod b)) as Heq.
  { apply Nat.div_mod; auto. lia. }
  rewrite <- Hmod in Heq; auto.
Qed.

Lemma mod_div_sub : ∀ a b c, b < a → 
  c mod (2 * a) = a + b → Nat.divide a (c - b).
Proof.
  intros a b y Hblta H.
  symmetry in H.
  apply mod_unique_rev with (a:=y) (b:=2 * a) (r:=a + b) in H.
  destruct H.
  rewrite H.
  assert (2 * a * x + (a + b) - b = (2 * x + 1) * a) as h by lia. rewrite h; clear h.
  apply Nat.divide_factor_r.
  lia.
Qed.

Lemma mod_div_add : ∀ a b c, b < a → 
  c mod (2 * a) = a - b → Nat.divide a (c + b).
Proof.
  intros a b y Hblta H.
  symmetry in H.
  apply mod_unique_rev with (a:=y) (b:=2 * a) (r:=a - b) in H.
  destruct H.
  rewrite H.
  assert (2 * a * x + (a - b) + b = (2 * x + 1) * a) as h by lia. rewrite h; clear h.
  apply Nat.divide_factor_r.
  lia.
Qed.

End Utility_Lemma.

Section KobayashiGardenTheorem_3xp1.

(* Relation of natural numbers *)
Definition Rdef (x y : nat) : Prop := 0 < x →
  (Nat.Odd x → y = 3 * x + 1) /\
  (Nat.Even x → y = x / 2).

Axiom R_Definition : ∀ x y, Rdef x y.

Definition R (x y : nat) := 0 < x → 
  (Nat.Odd x → 0 < y → y mod (2 * 3) = 4 → 
    y = 3 * x + 1 <-> (y - 1) / 3 = x) /\
  (Nat.Even x → x mod 2 = 0 →
    y = x / 2 <-> 2 * y = x).

Lemma Rf_correct (x y : nat) : R x y.
Proof.
  intros. split.
  + intros. split.
    - intros h.
      apply Nat.mul_cancel_l with (p:=3) (n:=((y - 1) / 3)) (m:=x); auto.
      rewrite <- Nat.divide_div_mul_exact; auto.
      rewrite Nat.mul_comm.
      rewrite Nat.div_mul; lia.
      apply mod_div_sub; auto.
    - intros h.
      apply Nat.mul_cancel_l with (p:=3) (n:=((y - 1) / 3)) (m:=x) in h; auto.
      rewrite <- Nat.divide_div_mul_exact in h; auto.
      rewrite Nat.mul_comm in h.
      rewrite Nat.div_mul in h; lia; auto.
      apply mod_div_sub; auto.
  + intros Heven Hmod. split.
    - intros Hx.
      apply Nat.mul_cancel_l with (p:=2) (n:=y) (m:=x / 2) in Hx; auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod;auto; rewrite <- Hmod in Hx; auto.
    - intros Hx.
      symmetry.
      apply Nat.mul_cancel_l with (p:=2) (n:=(x / 2)) (m:=y); auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod; auto; rewrite <- Hmod; auto.
Qed.

(* Function of natural numbers *)
Definition f (x : nat) : nat :=
  if Nat.odd x then 3 * x + 1 else x / 2.

(*
  c.f
    Software Foundation Version 6.2 (2022-08-28 10:19, Coq 8.15 or later)
      Inductively Defined Propositions (IndProp)
      https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html

      ''If you succeed in proving this conjecture, you've got a bright future as a number theorist. But don't spend too long on it -- it's been open since 1937!''
*)
Inductive reaches_1 : nat → Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) → reaches_1 n.

Lemma reaches_1_2 : reaches_1 2.
Proof. apply term_more; cbn; apply term_done. Qed.

Lemma reaches_1_3 : reaches_1 3.
Proof. do 7 apply term_more; cbn; apply term_done. Qed.

Lemma reaches_1_4 : reaches_1 4.
Proof. do 2 apply term_more; cbn; apply term_done. Qed.

Lemma reaches_1_5 : reaches_1 5.
Proof. do 5 apply term_more; cbn; apply term_done. Qed.

Lemma reaches_1_6 : reaches_1 6.
Proof. do 8 apply term_more; cbn; apply term_done. Qed.

Lemma min_rel_clos_reaches_1 :
  ∀ n : nat, 0 < n <= 2 * 3 → reaches_1 n.
Proof.
  intros n HnltModmin.
  assert (0 < n <= 2 * 3 → n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6) as H1to6 by lia.
  destruct H1to6 as [H1 | [H2 | [H3 | [H4 | [H5 | H6]]]]]; auto.
  - rewrite H1; apply term_done.
  - rewrite H2; apply reaches_1_2.
  - rewrite H3; apply reaches_1_3.
  - rewrite H4; apply reaches_1_4.
  - rewrite H5; apply reaches_1_5.
  - rewrite H6; apply reaches_1_6.
Qed.

(* Lemma to the relation *)
Lemma R_implies_f : ∀ x y, 0 < x → 
  ((Nat.Odd x → y = 3 * x + 1) /\ (Nat.Even x → y = x / 2)) →
  ((x <= 2 * 3 → reaches_1 x) → R x y → f x = y).
Proof.
  intros x y Hgt0 H. unfold f, R in *.
  - intros.
    destruct H as [Hodd Heven]; auto.
    case_eq (Nat.odd x).
    * rewrite Nat.odd_spec.
      symmetry; auto.
    * intros.
      assert (Nat.odd x = false → Nat.Even x) as Hodd_even 
      by (apply odd_false_even); apply Hodd_even in H;
      clear Hodd_even.
      apply Heven in H; auto.
Qed.

(* Lemma to the function *)
Lemma f_implies_R : ∀ x, R x (f x).
Proof. intros x. apply Rf_correct. Qed.

(* From the Collatz conjecture to the Kobayashi garden theorem *)
Theorem KobayashiGardenTheorem_AllNatReach1_3xp1_space : 
  ∀ n, 0 < n → reaches_1 n.
Proof.
  intros n Hngt0.
  constructor.
  assert (R n 1 → f n = 1) as H_R1_f1. {
    apply R_implies_f; auto.
    apply R_Definition; auto.
    intros; apply min_rel_clos_reaches_1; auto.
  }
  rewrite H_R1_f1. apply term_done.
  apply Rf_correct with (x:=n) (y:=1).
Qed.

End KobayashiGardenTheorem_3xp1.
