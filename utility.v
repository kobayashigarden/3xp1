Require Import Arith Lia Unicode.Utf8.

Theorem div_mul_inv : forall a b : nat, 0 < b -> a mod b = 0 -> 
  a = b * (a / b).
Proof. intros a b Hb Hmod. rewrite Nat.div_exact; lia. Qed.

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

Lemma odd_false: ∀ x : nat, 
  Nat.odd x = true → Nat.odd x = false → False.
Proof.
  intros x H1 H2.
  rewrite H1 in H2.
  discriminate H2.
Qed.

Lemma even_false: ∀ x : nat, Nat.odd x = true → Nat.even x = true → False.
Proof.
  intros x H1 H2.
  rewrite Nat.odd_spec in H1.
  rewrite Nat.even_spec in H2.
  assert (Nat.Even x → Nat.Odd x → False). {
    apply Nat.Even_Odd_False.
  } auto.
Qed.
