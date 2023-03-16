(*

Please use this URL when linking to this file.
https://doi.org/10.6084/m9.figshare.c.6472138

This proof file runs on Coq 8.16.
  https://coq.inria.fr/

### All theory and all implementation of this proof was developed entirely by Teruyuki and Yoko Kobayashi.
  This project began in May 2022 and was completed in March 2023.

  We have not been able to obtain the cooperation of any academic institution and therefore lack the funds.
  We need R&D funds. Please help us.

  Copyright Teruyuki and Yoko Kobayashi.
    https://orcid.org/0000-0002-5662-6948
    https://orcid.org/0000-0002-2704-3882

*)

Require Import Arith Lia Unicode.Utf8.

Section KobayashiGardenTheorem_3xn1.

(* Function of natural numbers *)
Definition f (x : nat) : nat :=
  if Nat.odd x then 3 * x - 1 else x / 2.

Inductive reaches_1 : nat → Prop :=
  | term_done : reaches_1 1
  | term_more (n : nat) : reaches_1 (f n) → reaches_1 n.

Axiom term_loop : forall n m, (reaches_1 (f n) <-> reaches_1 (f m)) -> ¬ reaches_1 n.

Lemma not_reaches_1_5 : ¬ reaches_1 5.
Proof.
  assert (reaches_1 (f 5) <-> reaches_1 (f 7)). {
    intros. split.
    - intros; do 3 apply term_more; cbn; auto.
    - intros; do 2 apply term_more; cbn; auto.
  }
  apply term_loop with (n:=5) (m:=7); auto.
Qed.

Require Import Coq.Logic.Classical.

(* The Kobayashi garden theorem 3x-1 space *)
Theorem KobayashiGardenTheorem_not_AllNatReach1_3xn1_space : 
  ¬ (forall n, reaches_1 n).
Proof.
  assert ((exists n, ¬ reaches_1 n) -> ¬ (forall n, reaches_1 n)). {
    intros H. apply ex_not_not_all; auto.
  } apply H.
  exists 5. apply not_reaches_1_5.
Qed.

End KobayashiGardenTheorem_3xn1.
