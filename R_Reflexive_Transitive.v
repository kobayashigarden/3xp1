Require Import Arith Lia Unicode.Utf8.
Require Import Coq.Classes.RelationClasses.

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

Definition R (x y : nat) := 0 < x -> 
  (Nat.Odd x -> 0 < y -> y mod 6 = 4 -> 
   y = 3 * x + 1 <-> (y - 1) / 3 = x) /\
  (Nat.Even x -> x mod 2 = 0 ->
   y = x / 2 <-> 2 * y = x).

Lemma R_Reflexive_f : Reflexive R.
Proof.
  unfold Reflexive. intros x.
  unfold R in *. split.
  + intros Hodd Hygt0 Hmod. 
    split.
    - intros.
      apply Nat.mul_cancel_l with (p:=3) (n:=((x - 1) / 3)) (m:=x); auto.
      rewrite <- Nat.divide_div_mul_exact; lia; auto.
    - intros h.
      apply Nat.mul_cancel_l with (p:=3) (n:=((x - 1) / 3)) (m:=x) in h; auto.
      rewrite <- Nat.divide_div_mul_exact in h; auto.
      rewrite Nat.mul_comm in h.
      rewrite Nat.div_mul in h; lia; auto.
      apply mod_div_sub; auto.
  + intros Heven Hmod. split.
    - intros Hx.
      apply Nat.mul_cancel_l with (p:=2) (n:=x) (m:=x / 2) in Hx; auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod;auto; rewrite <- Hmod in Hx; auto.
    - intros Hx.
      symmetry.
      apply Nat.mul_cancel_l with (p:=2) (n:=(x / 2)) (m:=x); auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod; auto; rewrite <- Hmod; auto.
Qed.

Lemma R_Transitive_f : Transitive R.
Proof.
  unfold Transitive. intros x y z Rxy Ryz.
  unfold R in *.
  split.
  + intros Hodd Hzgt0 Hmod.
    split.
    - intros h.
      apply Nat.mul_cancel_l with (p:=3) (n:=((z - 1) / 3)) (m:=x); auto.
      rewrite <- Nat.divide_div_mul_exact; auto.
      rewrite Nat.mul_comm; auto.
      rewrite Nat.div_mul; auto; lia.
      apply mod_div_sub; auto.
    - intros h.
      apply Nat.mul_cancel_l with (p:=3) (n:=((z - 1) / 3)) (m:=x) in h; auto.
      rewrite <- Nat.divide_div_mul_exact in h; auto.
      rewrite Nat.mul_comm in h.
      rewrite Nat.div_mul in h; lia; auto.
      apply mod_div_sub; auto.
  + intros Heven Hmod.
    split.
    - intros Hx.
      apply Nat.mul_cancel_l with (p:=2) (n:=z) (m:=x / 2) in Hx; auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod; auto. rewrite Hx; auto.
    - intros Hx.
      symmetry.
      apply Nat.mul_cancel_l with (p:=2) (n:=(x / 2)) (m:=z); auto.
      rewrite <- Nat.div_exact with (a:=x) (b:=2) in Hmod; auto; rewrite <- Hmod; auto.
  Qed.
