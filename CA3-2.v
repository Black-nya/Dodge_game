(** Load required packages.  Not all of these packages are needed right away,
    but they may be useful later. **)

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


(* Some useful lemmas.*)
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
intros.
rewrite A1.
rewrite A3.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P2 : \u2200 a : Z, -a + a = 0.
Proof.
intros.
rewrite A1.
rewrite A4.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P3 : \u2200 a : Z, 1 * a = a.
Proof.
intros.
rewrite M1 M3.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P4 : \u2200 a b : Z, a + b = 0 \u2192 b = -a.
Proof.
intros.
apply (S1 (a+b) 0 (-a)) in H.
rewrite A1P1 A1 A2 A1P2 A1P1 in H.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P5 : \u2200 a : Z, -(-a) = a.
Proof.
intros.
pose proof (A1P2 a).
pose proof (A1P4 (-a) a).
apply H0 in H.
symmetry.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P6 : \u2200 a : Z, 0 * a = 0.
Proof.
intros.
pose proof D1 0 0 a.
pose proof A3 0.
rewrite H0 in H.
apply (S1 (0*a) (0*a+0*a) (-(0*a))) in H.
rewrite A4 in H.
rewrite <- A2 in H.
rewrite A4 in H.
rewrite A3 in H.
symmetry.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P7 : \u2200 a : Z, -1 * a = -a.
Proof.
intros.
pose proof A1P6 a.
rewrite <- (A4 1) in H at 1.
rewrite D1 A1P3 in H.
apply (A1P4 a ((-1)*a)) in H.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P8 : \u2200 a b : Z, -a * -b = a * b.
Proof.
intros.
rewrite <- (A1P7 a).
rewrite <- (A1P7 b).
pose proof A1P5 1.
rewrite <-(A1P7 (-1)) in H.
rewrite (M1 (-1) a).
rewrite M2.
rewrite <- (M2 a (-1) (-1)).
rewrite H.
rewrite M3.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

Theorem A1P9 : \u2200 a b : Z, a + b = a \u2192 b = 0.
Proof.
intros.
apply (S1 (a+b) a (-a)) in H.
rewrite A1 A2 in H.
rewrite A1P2 A4 in H.
rewrite A1P1 in H.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)


Axiom A5 : \u2200 a b c : Z, a \u2260 0 \u2192 a*b = a*c \u2192 b = c.
Theorem A1P10 : \u2200 a b : Z, a \u2260 0 \u2192 a * b = a \u2192 b = 1.
Proof.
intros.
rewrite <- M3 in H0.
apply A5 in H0.
exact.
exact.
Qed. (* replace "Admitted." with "Qed." when your proof is finished. *)

(** The proof below is INCORRECT, even though Coq thinks it is correct.
    Find the error, and correct it. **)
Theorem A1P11 : \u2200 a b : Z, a * b = 0 \u2192 a = 0 \u2228 b = 0.
Proof.
  intros a b H.
  pose proof (classic (a=0)).
  destruct H0.
  left.
  exact.
  rewrite <- (A1P6 a) in H.
  rewrite (M1 0 a) in H.
  apply A5 in H.
  right.
  exact.
  exact.
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
  intros.
  unfold divide in H, H0.
  unfold divide.
  destruct H,H0.
  apply (S2 m (x0*a) x) in H.
  apply (S2 n (x1*a) y) in H0.
  apply (S1 (m*x) ((x0 * a) * x) (n*y)) in H.
  rewrite {2}H0 in H.
  rewrite -M2 -M2 in H.
  rewrite (M1 a x) (M1 a y) in H.
  rewrite M2 M2 in H.
  rewrite -D1 in H.
  exists ((x0*x)+(x1*y)).
  exact.
Qed.

Theorem A2P2: \u2200 a b c : Z, (a | b) \u2192 (b | c) \u2192 (a | c).
Proof.
  intros.
  unfold divide.
  unfold divide in H,H0.
  destruct H,H0.
  rewrite H in H0.
  rewrite M2 in H0.
  exists (x0*x).
  exact.
Qed.

Theorem A2P3 : \u2200 a b : Z, a < b \u2228 a = b \u2228 b < a.
Proof.
  intros.
  unfold lt.
  pose proof (G1 (b-a)).
  destruct H.
  + apply (S1 (b-a) 0 a) in H.
    rewrite -A2 in H.
    rewrite A1P2 in H.
    rewrite A3 A1P1 in H.
    right. left.
    exact.
  + destruct H.
    - left. exact.
    - assert (- (b - a) = (a-b)).
      pose proof (A1P7 (b-a)).
      rewrite M1 D1 in H0.
      rewrite M1 in H0.
      rewrite (M1 (-a) (-1)) in H0.
      rewrite A1P7 A1P7 in H0.
      rewrite A1P5 in H0.
      rewrite A1 in H0.
      exact.
      rewrite H0 in H.
      right. right.
      exact.
Qed.

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

Theorem A2P4 : \u2200 a b c : Z, a < b \u2192 0 < c \u2192 a * c < b * c.
Proof.
  intros.
  unfold lt.
  unfold lt in H,H0.
  unfold sub.
  rewrite -A1P7.
  rewrite M2.
  rewrite A1P7 -D1.
  rewrite <- (M3 (b-a)) in H.
  unfold sub in H0.
  rewrite -A1P7 M1 A1P6 A3 in H0.
  induction H0.
  exact H.
  apply (A2P6' ((b-a)*1) ((b-a)*n)) in IHpositive.
  rewrite (M1 (b-a) 1) (M1 (b-a) n) in IHpositive.
  rewrite -D1 M1 A1 in IHpositive.
  exact.
  exact.
Qed.

Theorem A2P5 : \u2200 a b c : Z, a * c = b * c \u2192 c \u2260 0 \u2192 a = b.
Proof.
intros.
apply (S1 (a*c) (b*c) (-(b*c))) in H.
rewrite A4 in H.
rewrite -A1P7 M2 A1P7 -D1 in H.
apply A1P11 in H.
destruct H.
+ rewrite A1 in H.
  apply A1P4 in H.
  rewrite A1P5 in H.
  exact.
+ contradiction.
Qed.

Theorem A2P6 : \u2200 a b c : Z, a < b \u2192 b < c \u2192 a < c.
Proof.
intros.
unfold lt in H,H0.
unfold lt.
apply (A2P6' (b-a) (c-b)) in H.
rewrite A1 in H.
rewrite A2 in H.
unfold sub in H.
rewrite <- (A2 c (-b) b) in H.
rewrite A1P2 A3 in H.
exact.
exact.
Qed.

Theorem A2P7 : \u2200 a : Z, \u00ac a < a.
Proof.
intros.
unfold lt,sub.
rewrite A4.
pose proof F1.
exact.
Qed.

Notation "2" := (1+1).
Theorem A2P8 : \u00ac (2 | 1).
Proof.
  intros.
  unfold divide,not.
  intros.
  destruct H.
  pose proof (A2P3 x 0).
  assert (\u2200 a : Z, (0<a)<-> positive a).
  intros.
  unfold iff.
  split.
  intros.
    unfold lt,sub in H1.
    rewrite -A1P7 M1 A1P6 A3 in H1.
    exact.
  intros.
    unfold lt,sub.
    rewrite -A1P7 M1 A1P6 A3.
    exact.
  assert (0<2).
  pose proof one_pos.
  apply add_pos in H2.
  apply H1 in H2.
  exact.
  assert ((1=0) \u2192 False).
  intros.
  pose proof one_pos.
  rewrite H3 in H4.
  pose proof F1.
  contradiction.
  destruct H0.
  + apply (A2P4 x 0 2) in H0.
      rewrite A1P6 in H0.
      rewrite -H in H0.
      unfold lt,sub in H0.
      rewrite A1P1 in H0.
      apply (add_pos (-1)) in H0.
      rewrite A1P2 in H0.
      pose proof F1.
      contradiction.
      exact.
  + destruct H0.
     rewrite H0 in H.
     rewrite A1P6 in H.
     apply H3 in H.
     exact.
    apply (H1 x) in H0.
     induction H0.
     rewrite A1P3 in H.
     apply (S1 1 2 (-1)) in H.
     rewrite A4 in H.
     rewrite -A2 in H.
     rewrite A4 in H.
     rewrite A3 in H.
     symmetry in H.
     apply H3 in H.
     exact.
     apply (S1 1 ((n + 1) * 2) (-1)) in H.
     rewrite A4 D1 in H.
     rewrite A1P3 in H.
     rewrite -A2 in H.
     rewrite <- (A2 1 1 (-1)) in H.
     rewrite A4 A3 in H.
     pose proof (A2P4 0 n 2).
     apply H1 in H0.
     pose proof (H4 H0 H2).
     rewrite A1P6 in H5.
     apply (H1 (n*2)) in H5.
     pose proof one_pos.
     pose proof ((A2P6' 1 (n*2)) H6 H5).
     rewrite A1 in H7.
     rewrite -H in H7.
     pose proof F1.
     contradiction.
Qed.

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

Lemma foo : \u2200 a : Z, (0<a)<-> positive a.
Proof.
  intros.
  unfold iff.
  split.
  intros.
    unfold lt,sub in H.
    rewrite -A1P7 M1 A1P6 A3 in H.
    exact.
  intros.
    unfold lt,sub.
    rewrite -A1P7 M1 A1P6 A3.
    exact.
Qed.

Lemma foofoo : \u2200 a b c: Z, a \u2264 b \u2192 a+c \u2264 b+c.
Proof.
  intros.
  unfold le in H.
  unfold le.
  destruct H.
    left.
  unfold lt in H.
  rewrite <- A3 in H.
  rewrite -A2 (A1 (-a) 0) in H.
  rewrite <- (A4 c) in H.
  rewrite -A2 in H.
  rewrite -A1P7 in H.
  rewrite <- (A1P7 a) in H.
  rewrite M1 (M1 (-1) a) -D1 M1 A1P7 A2 (A1 c a) in H.
  unfold lt.
  exact.
    right.
  apply (S1 a b c) in H.
  exact.
Qed.

Theorem A3P1 : 0 \u2260 1.
Proof.
  unfold not.
  intros.
  pose proof one_pos.
  rewrite -H in H0.
  pose proof F1.
  contradiction.
Qed.

Theorem A3P2 : \u2200 a b : Z, 0 < a \u2192 (0 < b \u2194 0 < a * b).
Proof.
  split.
  + intros.
    pose proof ((A2P4 0 a b) H H0).
    rewrite A1P6 in H1.
    exact.
  + intros.
    pose proof G1 b.
    destruct H1.
    rewrite H1 M1 A1P6 in H0.
    apply A2P7 in H0.
    contradiction.
    destruct H1.
    unfold lt,sub.
    rewrite -A1P7 M1 A1P6 A3.
    exact.
    assert ((-b)>0).
    unfold lt,sub.
    rewrite <- (A1P7 0).
    rewrite M1 A1P6 A3.
    exact.
    pose proof ((A2P4 0 a (-b)) H H2).
    rewrite A1P6 in H3.
    unfold lt,sub in H0,H3.
    rewrite -A1P7 (M1 (-1) 0) A1P6 A3 A3 in H0,H3.
    pose proof ((A2P6' (a*b) (a*(-b))) H0 H3).
    rewrite M1 (M1 a (-b)) -D1 in H4.
    rewrite A4 A1P6 in H4.
    pose proof F1.
    contradiction.
Qed.

Theorem A3P3a : \u2200 a b : Z, a < b \u2194 \u00ac b \u2264 a.
Proof.
  split.
  intros.
    unfold not,le.
    intros.
    destruct H0.
    pose proof ((A2P6 a b a) H H0).
    apply A2P7 in H1.
    exact.
    rewrite H0 in H.
    apply A2P7 in H.
    exact.
  intros.
    unfold not,le in H.
    pose proof (A2P3 a b).
    destruct H0.
    exact.
    assert ((b < a) \u2228 (b = a)).
    destruct H0.
    right.
    exact.
    left.
    exact.
    apply H in H1.
    exact.
Qed.

Theorem A3P3b : \u2200 a b : Z, a \u2264 b \u2194 \u00ac b < a.
Proof.
  split.
  unfold not.
  intros.
  unfold le in H.
  destruct H.
    pose proof ((A2P6 a b a) H H0).
    apply A2P7 in H1.
    exact.
    rewrite H in H0.
    apply A2P7 in H0.
    exact.
  unfold not.
  intros.
  unfold le.
  pose proof (A2P3 a b).
  destruct H0.
  left. exact.
  destruct H0.
  right. exact.
  apply H in H0.
  exact.
Qed.

Theorem A3P4 : \u2200 a : Z, 0 < a \u2192 \u00ac a < 1.
Proof.
  intros.
  assert (\u2200 a : Z, (0<a)<-> positive a).
  intros.
  unfold iff.
  split.
  intros.
    unfold lt,sub in H0.
    rewrite -A1P7 M1 A1P6 A3 in H0.
    exact.
  intros.
    unfold lt,sub.
    rewrite -A1P7 M1 A1P6 A3.
    exact.
  apply (H0 a) in H.
  induction H.
  pose proof (A2P7 1).
  exact.
  apply A3P3b in IHpositive.
  apply A3P3b.
  unfold le in IHpositive.
  unfold le.
  destruct IHpositive.
  left.
  unfold lt,sub.
  rewrite -A2 A4 A3.
  exact.
  left.
  rewrite -H1.
  unfold lt,sub.
  rewrite -A2 A4 A3.
  pose proof one_pos.
  exact. 
Qed.

Theorem A3P5 : \u2200 a b : Z, (a | b) \u2192 (b>0 \u2192 (a\u2264b)\u2227(-a)\u2264b)\u2227(b<0 \u2192 a\u2264(-b)\u2227(-a)\u2264(-b)).
Proof.
  assert (\u2200 a b : Z, (a | b) \u2192 (b>0 \u2192 (a\u2264b))).
  intros.
  unfold divide in H.
  destruct H.
  pose proof (classic (a\u2264b)).
  destruct H1.
    exact.
    apply A3P3a in H1.
      pose proof ((A2P6 0 b a) H0 H1).
      rewrite H M1 in H0.
      pose proof ((A3P2 a x) H2).
      apply H3 in H0.
      apply A3P4,A3P3b in H0.
      unfold le in H0.
      destruct H0.
        pose proof ((A2P4 1 x a) H0 H2).
      rewrite A1P3 -H in H4.
      pose proof ((A2P6 b a b) H1 H4).
      pose proof (A2P7 b).
      contradiction.
        rewrite -H0 A1P3 in H.
      rewrite H in H1.
      pose proof (A2P7 a).
      contradiction.
  intros.
  split.
    split.
     pose proof ((H a b) H0 H1).
      exact.
     destruct H0.
     rewrite <- (A1P8 x a) in H0.
     assert (- a | b).
     unfold divide.
     exists (-x).
     exact.
     pose proof ((H (-a) b) H2 H1).
     exact.
    intros.
     unfold lt,sub in H1.
     rewrite A1P1 in H1.
     apply foo in H1.
    split.
     assert (a|(-b)).
       unfold divide in H0.
       destruct H0.
       apply (S2 b (x*a) (-1)) in H0.
       rewrite M1 A1P7 M1 M2 A1P7 in H0.
       unfold divide.
       exists (-x).
       exact.
     pose proof ((H a (-b)) H2 H1).
     exact.
     assert ((-a)|(-b)).
      unfold divide in H0.
      destruct H0.
      apply (S2 b (x*a) (-1)) in H0.
      rewrite M1 A1P7 -M2 (M1 a(-1)) A1P7 in H0.
      unfold divide.
      exists x.
      exact.
     pose proof ((H (-a) (-b))H2 H1).
     exact.
Qed.

Lemma fo : \u2200 a b : Z, (b\u2264a\u2264b) \u2192 a=b.
Proof.
  intros.
  unfold le in H.
  destruct H.
  pose proof (A2P7 b).
  destruct H,H0.
  pose proof ((A2P6 b a b) H H0).
  contradiction.
  rewrite H0 in H.
  contradiction.
  rewrite -H in H0.
  contradiction.
  exact.
Qed.
    
Theorem A3P6 : \u2200 a : Z, unit a \u2194 a = \u00b1 1.
Proof.
  split.
  + intros.
    unfold unit in H.
    pose proof (A3P5 a 1) H.
    destruct H0.
    pose proof one_pos.
    apply foo in H2.
    apply H0 in H2.
    unfold pm.
    destruct H2.
    pose proof (classic(a>0)).
    destruct H4.
      - apply A3P4,A3P3b in H4.
      pose proof (fo a 1).
      destruct H5.
      split.
      exact. exact.
      left.
      exact.
    - apply (A3P3b a 0) in H4.
    unfold le in H4.
    destruct H4.
    * unfold lt,sub in H4.
    rewrite A1P1 in H4.
    apply foo in H4.
    apply A3P4,A3P3b in H4.
    pose proof (fo (-a) 1).
    destruct H5.
      split.
      exact. 
      exact.
      right.
      pose proof (A1P5 a).
      exact.
    * unfold divide in H.
      rewrite H4 in H.
      destruct H.
      rewrite M1 A1P6 in H.
      pose proof A3P1.
      symmetry in H.
      contradiction.
  + intros.
    unfold unit, divide.
    destruct H.
    exists 1.
    rewrite H M3.
    exact.
    exists (-1).
    rewrite H.
    rewrite A1P8 M3.
    exact.
Qed.
Lemma sto: \u2200 a b: Z, a<b -> a \u2264 (b-1).
Proof.  
  intros.
  unfold le.
  pose proof (classic (a=b-1)).
  destruct H0.
  right.
  exact.
  apply foo in H.
  apply A3P4 in H.
  apply A3P3b in H.
  unfold le in H.
  destruct H.
  left.
  unfold lt.
  unfold lt in H.
  unfold sub in H at 1.
  rewrite -A2 in H.
  unfold sub at 2 1.
  rewrite -A2 (A1 (-1) (-a)).
  exact.
  apply (S1 1 (b-a) (a-1)) in H.
  rewrite A1 -A2 A1P2 A3 in H.
  unfold sub in H.
  rewrite A2 -(A2 b (-a) a) A1P2 A3 in H.
  exact.
Qed.
(* Strong Induction *)
Theorem A3P7 : \u2200 P : Z \u2192 Prop,
                                         (\u2200 n, (\u2200 k, 0 < k < n \u2192 P k) \u2192 P n) \u2192 \u2200 n, P n.
Proof.
  intros.
  pose proof (G1 n).
  destruct H0.
  apply H.
  intros.
  rewrite H0 in H1.
  destruct H1.
  pose proof (A2P6 0 k 0) H1 H2.
  apply A2P7 in H3.
  exact.
  destruct H0.
  assert (P 1).
  apply H.
  intros.
  destruct H1.
  apply A3P4 in H1.
  exact.
  assert (P 2).
  apply H.
  intros.
  destruct H2.
  apply A3P4 in H2.
  apply A3P3b in H2.
  apply sto in H3.
  unfold sub in H3.
  rewrite -A2 A4 A3 in H3.
  pose proof (fo k 1).
  destruct H4.
  split.
  exact.
  exact.
  exact.
  
  induction H0.
  exact.
  apply H.
  intros.
  destruct H3.
  apply sto in H4.
  unfold sub in H4.
  rewrite -A2 A4 A3 in H4.
  apply (foo k) in H3.
  induction H3.
  exact.
  
  induction H0.
  exact.
  
  apply H.
  intros.
  destruct H3.
  apply H.
  intros.
  destruct H2.
  apply (foo k) in H2.
  induction H2.
  exact.
  pose proof (classic (n0+1=n)).
  destruct H4.
  rewrite H4.
  exact.
  
Admitted.

(* Well-ordering principle *)
(* NOTE: you can deploy strong induction to prove (\u2200 n, P n) by using the command "induction n using A3P7." *)
Theorem A3P8 : \u2200 S : Z \u2192 Prop, (\u2200 x : Z, S x \u2192 0 < x) \u2192 (\u2203 x : Z, S x) \u2192
                               \u2203 s : Z, S s \u2227 \u2200 t : Z, S t \u2192 s \u2264 t.
Proof.
 intros.
  destruct H0.
  apply NNPP.
  unfold not at 1.
  intros.
  enough (\u2200 z, 0 < z < x + 1 \u2192 \u00ac S z).
Admitted.