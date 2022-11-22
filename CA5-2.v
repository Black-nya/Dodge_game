(** Load required packages.  Not all of these packages are needed right away,
    but they may be useful later. **)

Require Export Setoid List Ring Sorted Constructive_sets Utf8_core Wf_nat
        ProofIrrelevance Permutation IndefiniteDescription ChoiceFacts
        ClassicalEpsilon ssrfun ssrbool ssreflect.

(** Math symbols for cut and paste: \u2200 \u2203 \u2192 \u2194 \u2227 \u2228 \u00ac \u2260 \u2264 \u2265 \u2205 \u2115 \u2124 \u2208 \u2209 \u2282 \u2211 \u220f \u03bb **)

(** Axioms for the integers. **)

Parameter Z : Set.

Parameter add mult : Z \u2192 Z \u2192 Z.
Parameter neg : Z \u2192 Z.
Parameter zero one : Z.
Notation "0" := zero.
Notation "1" := one.
Infix "+" := add.
Infix "*" := mult.
Notation "- x" := (neg x).
Notation "- 0" := (neg 0).
Notation "- 1" := (neg 1).
Definition sub (a b : Z) := a + -b.
Infix "-" := sub.

Axiom A1 : \u2200 a b   : Z, a + b = b + a.
Axiom A2 : \u2200 a b c : Z, a + (b + c) = (a + b) + c.
Axiom A3 : \u2200 a     : Z, a + 0 = a.
Axiom A4 : \u2200 a     : Z, a + -a = 0.
Axiom M1 : \u2200 a b   : Z, a * b = b * a.
Axiom M2 : \u2200 a b c : Z, a * (b * c) = (a * b) * c.
Axiom M3 : \u2200 a     : Z, a * 1 = a.
Axiom D1 : \u2200 a b c : Z, (a + b) * c = a * c + b * c.

(** Some useful lemmas. **)

Lemma S1 : \u2200 a b c : Z, a = b \u2192 a + c = b + c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

Lemma S2 : \u2200 a b c : Z, a = b \u2192 a * c = b * c.
Proof.
  intros a b c H.
  rewrite H.
  reflexivity.
Qed.

(** Homework assignment problems are given below. **)

Theorem A1P1 : \u2200 a : Z, 0 + a = a.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P2 : \u2200 a : Z, -a + a = 0.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P3 : \u2200 a : Z, 1 * a = a.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P4 : \u2200 a b : Z, a + b = 0 \u2192 b = -a.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P5 : \u2200 a : Z, -(-a) = a.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P6 : \u2200 a : Z, 0 * a = 0.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P7 : \u2200 a : Z, -1 * a = -a.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P8 : \u2200 a b : Z, -a * -b = a * b.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P9 : \u2200 a b : Z, a + b = a \u2192 b = 0.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P10 : \u2200 a b : Z, a * b = a \u2192 b = 1.
Proof.
Admitted. (* replace "Admitted." with "Qed." when your proof is finished. *)

(** The proof below is INCORRECT, even though Coq thinks it is correct.
    Find the error, and correct it. **)
Theorem A1P11 : \u2200 a b : Z, a * b = 0 \u2192 a = 0 \u2228 b = 0.
Proof.
  intros a b H.
  apply (S1 (a*b) 0 (1*b)) in H.
  rewrite -D1 in H.
  rewrite A1P3 in H.
  rewrite A1P1 in H.
  rewrite M1 in H.
  apply A1P10 in H.
  apply (S1 (a+1) 1 (-1)) in H.
  rewrite -A2 in H.
  rewrite A4 in H.
  rewrite A3 in H.
  left.
  exact H.
Qed.

Inductive positive : Z \u2192 Prop :=
| one_pos : positive 1
| add_pos n : positive n \u2192 positive (n + 1).

Axiom F1 : \u00ac positive 0.
Axiom G1 : \u2200 a : Z, a = 0 \u2228 positive a \u2228 positive (-a).

Definition lt a b := positive (b - a).
Infix "<" := lt.
Notation "a > b" := (b < a) (only parsing).

Definition divide (x y : Z) := \u2203 z : Z, y = z * x.
Notation "( x | y )" := (divide x y).

Theorem A2P1 : \u2200 a m n x y : Z, (a | m) \u2192 (a | n) \u2192 (a | m * x + n * y).
Proof.
Admitted.

Theorem A2P2: \u2200 a b c : Z, (a | b) \u2192 (b | c) \u2192 (a | c).
Proof.
Admitted.

Theorem A2P3 : \u2200 a b : Z, a < b \u2228 a = b \u2228 b < a.
Proof.
Admitted.

Theorem A2P4 : \u2200 a b c : Z, a < b \u2192 0 < c \u2192 a * c < b * c.
Proof.
Admitted.

Theorem A2P5 : \u2200 a b c : Z, a * c = b * c \u2192 c \u2260 0 \u2192 a = b.
Proof.
Admitted.

(* NOTE: you can deploy induction on a hypothesis "H: positive a." by using the command "induction H." *)
Lemma A2P6' : \u2200 a b : Z, positive a \u2192 positive b \u2192 positive (a+b).
Proof.
  intros.
  induction H0.
  apply (add_pos a) in H.
  exact H.
  apply (add_pos (a + n)) in IHpositive.
  rewrite <- A2 in IHpositive.
  exact IHpositive.
Qed.

Theorem A2P6 : \u2200 a b c : Z, a < b \u2192 b < c \u2192 a < c.
Proof.
Admitted.

Theorem A2P7 : \u2200 a : Z, \u00ac a < a.
Proof.
Admitted.

Notation "2" := (1+1).
Theorem A2P8 : \u00ac (2 | 1).
Proof.
Admitted.

Definition le a b := a < b \u2228 a = b.
Infix "\u2264" := le (at level 70).
Notation "a \u2265 b" := (b \u2264 a) (at level 70, only parsing).
Notation "a < b < c" := (a < b \u2227 b < c).
Notation "a \u2264 b < c" := (a \u2264 b \u2227 b < c) (at level 70, b at next level).
Notation "a < b \u2264 c" := (a < b \u2227 b \u2264 c) (at level 70, b at next level).
Notation "a \u2264 b \u2264 c" := (a \u2264 b \u2227 b \u2264 c) (at level 70, b at next level).

Definition pm (a b : Z) := (a = b \u2228 a = -b).
Notation "a = \u00b1 b" := (pm a b) (at level 60).
Notation "x \u2260 \u00b1 y" := (\u00ac (x = \u00b1 y)) (at level 60).
Definition assoc (a b : Z) := (a | b) \u2227 (b | a).
Infix "~" := assoc (at level 70).
Definition unit a := (a | 1).

Theorem A3P1 : 0 \u2260 1.
Proof.
Admitted.

Theorem A3P2 : \u2200 a b : Z, 0 < a \u2192 (0 < b \u2194 0 < a * b).
Proof.
Admitted.

Theorem A3P3a : \u2200 a b : Z, a < b \u2194 \u00ac b \u2264 a.
Proof.
Admitted.

Theorem A3P3b : \u2200 a b : Z, a \u2264 b \u2194 \u00ac b < a.
Proof.
Admitted.

Theorem A3P4 : \u2200 a : Z, 0 < a \u2192 \u00ac a < 1.
Proof.
Admitted.

Theorem A3P5 : \u2200 a b : Z, (a | b) \u2192 a \u2264 b.
Proof.
Admitted.

Theorem A3P6 : \u2200 a : Z, unit a \u2194 a = \u00b1 1.
Proof.
Admitted.

(* Strong Induction *)
Theorem A3P7 : \u2200 P : Z \u2192 Prop,
                                         (\u2200 n, (\u2200 k, 0 < k < n \u2192 P k) \u2192 P n) \u2192 \u2200 n, P n.
Proof.
Admitted.

(* Well-ordering principle *)
(* NOTE: you can deploy strong induction to prove (\u2200 n, P n) by using the command "induction n using A3P7." *)
Theorem A3P8 : \u2200 S : Z \u2192 Prop, (\u2200 x : Z, S x \u2192 0 < x) \u2192 (\u2203 x : Z, S x) \u2192
                               \u2203 s : Z, S s \u2227 \u2200 t : Z, S t \u2192 s \u2264 t.
Proof.
Admitted.

Add Ring Z_ring : (mk_rt _ _ _ _ _ _ _ A1P1 A1 A2 A1P3 M1 M2 D1
                         (\u03bb a b : Z, erefl (a - b)) A4).

(* Definition and properties of absolute value. *)

Definition abs a : Z :=
  if excluded_middle_informative (0 < a) then a else (-a).

Notation "| a |" := (abs a) (at level 35, format "'|' a '|'").
Notation "|- a |" := (abs (neg a)) (at level 35, format "'|-' a '|'").

Lemma abs_pos : \u2200 a : Z, 0 < a \u2192 |a| = a.
Proof.
  intros a H.
  unfold abs.
  destruct excluded_middle_informative; simpl; auto.
  contradiction.
Qed.

Lemma abs_neg : \u2200 a : Z, a < 0 \u2192 |a| = -a.
Proof.
  intros a H.
  unfold abs.
  destruct excluded_middle_informative; simpl; auto.
  contradiction (A2P7 a); eauto using A2P6.
Qed.

Lemma abs_zero : |0| = 0.
Proof.
  unfold abs.
  destruct excluded_middle_informative; simpl; auto.
  ring.
Qed.

Lemma abs_pm : \u2200 a : Z, |a| = \u00b1 a.
Proof.
  intros a.
  unfold abs, pm.
  destruct excluded_middle_informative; auto.
Qed.

Theorem A4P1 : \u2200 a : Z, |a| = |-a|.
Proof.
Admitted.

Theorem A4P2 : \u2200 a : Z, 0 \u2264 |a|.
Proof.
Admitted.

Theorem A4P3 : \u2200 a : Z, a \u2264 |a|.
Proof.
Admitted.

Theorem A4P4 : \u2200 a b : Z, a ~ b \u2194 \u2203 u : Z, unit u \u2227 b = a * u.
Proof.
Admitted.

Theorem A4P5 : \u2200 a b : Z, a ~ b \u2194 a = \u00b1 b.
Proof.
Admitted.

Theorem A4P6 : \u2200 a b : Z, (a | b) \u2192 b \u2260 0 \u2192 a \u2264 |b|.
Proof.
Admitted.

(* Division algorithm *)
Theorem A4P7 : \u2200 a b : Z, 0 < a \u2192 0 < b \u2192 \u2203 q r : Z, a = b * q + r \u2227 0 \u2264 r < b.
Proof.
Admitted.

(* "Relatively prime" *)
Definition rel_prime (a b : Z) := \u2200 d : Z, (d | a) \u2192 (d | b) \u2192 unit d.

Theorem rel_prime_sym : \u2200 a b : Z, rel_prime a b \u2194 rel_prime b a.
Proof.
  firstorder.
Qed.

Theorem rel_prime_1 : \u2200 a : Z, rel_prime a 1.
Proof.
  firstorder.
Qed.
Lemma lm4: \u2200 a b : Z, a=-b -> -a = b.
Proof.
  intros.
  rewrite H.
  rewrite A1P5.
  exact.
Qed.
Lemma lm1: \u2200 a b : Z, (a|b) <-> (a|(-b)).
Proof.
  unfold divide.
  split.
  intros.
  destruct H.
  exists (-x).
  rewrite <- (A1P5 (x*a)) in H.
  apply lm4 in H.
  rewrite <- (A1P7 (x*a)) in H. 
  rewrite M2 A1P7 in H.
  exact.
  intros.
  destruct H.
  symmetry in H.
  apply (lm4 (x*a) b) in H.
  symmetry in H.
  exists (-x).
  rewrite <- (A1P7 (x*a)) in H.
  rewrite M2 A1P7 in H.
  exact.
Qed.
Theorem A5P1 : \u2200 a : Z, rel_prime a 0 \u2194 unit a.
Proof.
  unfold rel_prime.
  split.
  intros.
  apply H.
  unfold divide.
  exists 1.
  rewrite A1P3.
  exact.
  unfold divide.
  exists 0.
  rewrite A1P6.
  exact.
  intros.
  apply A3P6 in H.
  destruct H.
  rewrite H in H0.
  unfold unit.
  exact.
  rewrite H in H0.
  apply lm1 in H0.
  unfold unit.
  exact.
Qed.

Theorem A5P2 : \u2200 a b : Z, rel_prime a b \u2194 rel_prime a (-b).
Proof.
  unfold rel_prime.
  split.
  intros.
  apply H.
  exact.
  apply lm1 in H1.
  exact.
  intros.
  apply H.
  exact.
  apply lm1 in H1.
  exact.
Qed.

Theorem A5P3 : \u2200 a b c : Z, (a | b) \u2192 rel_prime b c \u2192 rel_prime a c.
Proof.
  unfold rel_prime.
  intros.
  apply H0.
  pose proof (A2P2 d a b) H1 H.
  exact.
  exact.
Qed.


(* Euclidean algorithm / Bezout's lemma *)
Theorem A5P4 : \u2200 a b : Z, rel_prime a b \u2192 \u2203 x y, a * x + b * y = 1.
Proof.
  unfold rel_prime.
  intros.
  
  pose proof (classic (\u2203 x y, a * x + b * y = 1)).
  destruct H0.
  exact.
  
  assert (\u2200 x y : Z, (((a * x) + (b * y)) \u2260  1)).
  pose proof (classic (\u2200 x y : Z, (((a * x) + (b * y)) \u2260  1))).
  destruct  H1.
  exact.
  unfold not.
  intros.
  unfold not in H0.
  apply H0.
  exists x,y.
  exact.
  destruct H0.
  unfold not in H1.
Admitted.

(* Gauss's lemma *)
Theorem A5P5 : \u2200 a b c : Z, rel_prime a b \u2192 (a | b * c) \u2192 (a | c).
Proof.
Admitted.

Theorem A5P6 : \u2200 a b c : Z, rel_prime a b \u2192 (a | c) \u2192 (b | c) \u2192 (a * b | c).
Proof.
Admitted.

Theorem A5P7 : \u2200 a b c : Z, rel_prime a c \u2192 rel_prime b c \u2192 rel_prime (a*b) c.
Proof.
Admitted.