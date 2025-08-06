From QuantumLib Require Import Matrix.
From QuantumLib Require Import Quantum.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_0_l c : 0 / c = 0.
Proof. apply Cmult_0_l. Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_nonzero_iff (c d : C) : 
  d / c <> 0 <-> c <> 0 /\ d <> 0.
Proof.
  rewrite Cdiv_integral_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_nonzero_iff_r (c d : C) : c <> 0 ->
  d / c <> 0 <-> d <> 0.
Proof.
  intros Hc.
  rewrite Cdiv_nonzero_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cmult_nonzero_iff (c d : C) : 
  c * d <> 0 <-> c <> 0 /\ d <> 0.
Proof.
  rewrite Cmult_integral_iff.
  tauto.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cinv_div (c d : C) : 
  / (c / d) = d / c.
Proof.
  unfold Cdiv.
  rewrite Cinv_mult_distr, Cinv_inv.
  apply Cmult_comm.
Qed.

(* @nocheck name *)
(* Conventional name *)
Lemma Cdiv_div (b c d : C) : 
  b / (c / d) = b * d / c.
Proof.
  unfold Cdiv at 1.
  rewrite Cinv_div.
  apply Cmult_assoc.
Qed.