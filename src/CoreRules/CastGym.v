
Require Import CoreData.CoreData.
Require Import CastRules.
Require Import ComposeRules.


Lemma cast0 : forall n m prfn prfm (zx : ZX n m),
  cast (2 + 0)  (2 + 0) prfn prfm ⨉ ∝ ⨉.
Proof.
  intros.
    idtac "acdc-solution". (* Begin ACDC generated solution *)
    erewrite (cast_id _ _ (Swap)). (* (Swap) *) (* FROM *) (* (cast undefined undefined (Swap)}) *)
    reflexivity. (* End ACDC generated solution *)
Admitted.

Lemma cast1: forall n m o p prf1 prf2 prf3 prf4 (zx0 : ZX n m) (zx1 : ZX m o), cast (n + (p + 1)) (o + (p + 1)) prf1 prf2 (cast (n + (S p)) (m + (S p)) prf3 prf4 (zx0 ⟷ zx1 ↕ (n_wire p ↕ —))) ∝ ( zx0 ⟷ zx1 ↕ (n_wire p ↕ —)).
Proof.
intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite -> (cast_contract _ _ _ _ _ _ (Stack (Compose (zx0) (zx1)) (Stack (n_wire (p)) (Wire)))). (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (Stack (Compose (zx0) (zx1)) (Stack (nwire (p)) (Wire)))}) *) (* FROM *) (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (cast ((n) + (1 + (p))%nat)%nat ((m) + (1 + (p))%nat)%nat (Stack (Compose (zx0) (zx1)) (Stack (nwire (p)) (Wire)))})}) *)
erewrite -> (cast_id _ _ (Stack (Compose (zx0) (zx1)) (Stack (n_wire (p)) (Wire)))). (* (Stack (Compose (zx0) (zx1)) (Stack (nwire (p)) (Wire))) *) (* FROM *) (* (cast undefined undefined (Stack (Compose (zx0) (zx1)) (Stack (nwire (p)) (Wire)))}) *)
  reflexivity. (* End ACDC generated solution *)
Admitted.

Lemma cast2: ( forall n m o p prf1 prf2 prf3 prf4 prf5 prf6(zx0 : ZX n m) (zx1 : ZX m o), cast (n + (p + 1)) (o + (p + 1)) prf1 prf2 ((cast (n + (S p)) (m + (S p)) prf3 prf4 (zx0 ↕ (n_wire p ↕ —))) ⟷ (cast (m + (S p)) (o + (S p)) prf5 prf6 (zx1 ↕ (n_wire p ↕ —)))) ∝ zx0 ↕ (n_wire p ↕ —) ⟷ (zx1 ↕ (n_wire p ↕ —))).
Proof.
intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite <- (cast_compose_mid_contract _ _ _ _ _ _ _ _ _ (Stack (zx0) (Stack (n_wire (p)) (Wire))) (Stack (zx1) (Stack (n_wire (p)) (Wire)))). (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (cast ((n) + (1 + (p))%nat)%nat ((o) + (1 + (p))%nat)%nat (Compose (Stack (zx0) (Stack (nwire (p)) (Wire))) (Stack (zx1) (Stack (nwire (p)) (Wire))))})}) *) (* FROM *) (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (Compose (cast ((n) + (1 + (p))%nat)%nat ((m) + (1 + (p))%nat)%nat (Stack (zx0) (Stack (nwire (p)) (Wire)))}) (cast ((m) + (1 + (p))%nat)%nat ((o) + (1 + (p))%nat)%nat (Stack (zx1) (Stack (nwire (p)) (Wire)))}))}) *)
erewrite -> (cast_contract _ _ _ _ _ _ (Compose (Stack (zx0) (Stack (n_wire (p)) (Wire))) (Stack (zx1) (Stack (n_wire (p)) (Wire))))). (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (Compose (Stack (zx0) (Stack (nwire (p)) (Wire))) (Stack (zx1) (Stack (nwire (p)) (Wire))))}) *) (* FROM *) (* (cast ((n) + ((p) + (1 + 0)%nat)%nat)%nat ((o) + ((p) + (1 + 0)%nat)%nat)%nat (cast ((n) + (1 + (p))%nat)%nat ((o) + (1 + (p))%nat)%nat (Compose (Stack (zx0) (Stack (nwire (p)) (Wire))) (Stack (zx1) (Stack (nwire (p)) (Wire))))})}) *)
erewrite (cast_id _ _ (Compose (Stack (zx0) (Stack (n_wire (p)) (Wire))) (Stack (zx1) (Stack (n_wire (p)) (Wire))))). (* (Compose (Stack (zx0) (Stack (nwire (p)) (Wire))) (Stack (zx1) (Stack (nwire (p)) (Wire)))) *) (* FROM *) (* (cast undefined undefined (Compose (Stack (zx0) (Stack (nwire (p)) (Wire))) (Stack (zx1) (Stack (nwire (p)) (Wire))))}) *)
  reflexivity. (* End ACDC generated solution *)

Admitted.
Hint Rewrite @cast_stack_distribute : cast_simpl_db.
Hint Rewrite @cast_contract_r : cast_simpl_db.
Hint Rewrite @cast_compose_r @cast_compose_l: cast_simpl_db.
(* Hint Rewrite <- @cast_compose_mid: cast_simpl_db.  *)
Print Rewrite HintDb cast_simpl_db.


(* $ S (S (S n)), S (S (S n))
  ::: ⨉ ↕ n_wire n ⟷ (— ↕ top_to_bottom_helper n) ↕ — $
  ⟷ $ S (S (S n)), S (S (S n))
    ::: $ 1 + n + 2, 1 + n + 2 ::: — ↕ (n_wire n ↕ ⨉) $ $ *)

(* $ S (S (S n)), S (S (S n))
  ::: $ 2 + n, S (S n) ::: ⨉ ↕ n_wire n $
      ⟷ (— ↕ $ S n, S n ::: top_to_bottom_helper n $) ↕ — $
  ⟷ (— ↕ $ S (S n), S (S n) ::: n_wire n ↕ ⨉ $) *)

Lemma cast3: forall n prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8 prf9 prf10 prf11 prf12 prf13 prf14,
cast (S (S (S n))) (((S (S (S n))))) prf1 prf2 
(⨉ ↕ n_wire n ⟷ (— ↕ n_wire (S n)) ↕ —)  ⟷ 
cast (S (S (S n))) (((S (S (S n))))) prf3 prf4 
((cast (1 + n +2) (1 + n + 2) prf5 prf6 
(— ↕ (n_wire n ↕ ⨉)))) ∝ 
cast (S (S (S n))) (((S (S (S n))))) prf7 prf8 
((cast (2 + n) (S (S n)) prf9 prf10 
(⨉ ↕ n_wire n)) ⟷ 
(— ↕ (cast (S n) (S n) prf11 prf12 (n_wire (S n)))) ↕ —) ⟷ 
(— ↕ (cast (S (S n)) (S (S n)) prf13 prf14 (n_wire n ↕ ⨉) )).
Proof. (* TODO Debug *)
intros.




Admitted.

(* $ S (S (S n)), S (S n) + 1 ::: ⨉ ↕ n_wire n ↕ — $
⟷ $ S (S n) + 1, S (S (S n)) ::: — ↕ top_to_bottom_helper n ↕ — $ *)
(*$ S (S (S n)), S (S (S n)) ::: ⨉ ↕ n_wire n ↕ — $
⟷ $ S (S (S n)), S (S (S n)) ::: — ↕ top_to_bottom_helper n ↕ — $*)

Lemma cast4 : forall n prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8,
cast (S (S (S n))) (S (S n) + 1) prf1 prf2 
(⨉ ↕ n_wire n ↕ —) ⟷ 
cast _ (S (S (S n))) prf3 prf4 
(— ↕ n_wire (S n) ↕ —) ∝
cast (S (S (S n))) (S (S (S n))) prf5 prf6 
(⨉ ↕ n_wire n ↕ —) ⟷ 
cast (S (S (S n))) (S (S (S n))) prf7 prf8 
(— ↕ n_wire (S n) ↕ —).
Proof.
  intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite <- (cast_compose_mid_contract _ _ _ _ _ _ _ _ _ (Stack (Stack (Swap) (n_wire (n))) (Wire)) (Stack (Stack (Wire) (n_wire (1 + (n))%nat)) (Wire))). (* (cast (1 + (1 + (1 + (n))%nat)%nat)%nat (1 + (1 + (1 + (n))%nat)%nat)%nat (Compose (Stack (Stack (Swap) (nwire (n))) (Wire)) (Stack (Stack (Wire) (nwire (1 + (n))%nat)) (Wire)))}) *) (* FROM *) (* (Compose (cast (1 + (1 + (1 + (n))%nat)%nat)%nat ((1 + (1 + (n))%nat)%nat + (1 + 0)%nat)%nat (Stack (Stack (Swap) (nwire (n))) (Wire))}) (cast ((1 + (1 + (n))%nat)%nat + (1 + 0)%nat)%nat (1 + (1 + (1 + (n))%nat)%nat)%nat (Stack (Stack (Wire) (nwire (1 + (n))%nat)) (Wire))})) *)
erewrite -> (cast_compose_mid_contract  _ _ _ _ _ _ _ _ _  (Stack (Stack (Swap) (n_wire (n))) (Wire)) (Stack (Stack (Wire) (n_wire (1 + (n))%nat)) (Wire))). (* (Compose (cast (1 + (1 + (1 + (n))%nat)%nat)%nat (1 + (1 + (1 + (n))%nat)%nat)%nat (Stack (Stack (Swap) (nwire (n))) (Wire))}) (cast (1 + (1 + (1 + (n))%nat)%nat)%nat (1 + (1 + (1 + (n))%nat)%nat)%nat (Stack (Stack (Wire) (nwire (1 + (n))%nat)) (Wire))})) *) (* FROM *) (* (cast (1 + (1 + (1 + (n))%nat)%nat)%nat (1 + (1 + (1 + (n))%nat)%nat)%nat (Compose (Stack (Stack (Swap) (nwire (n))) (Wire)) (Stack (Stack (Wire) (nwire (1 + (n))%nat)) (Wire)))}) *)
  reflexivity. (* End ACDC generated solution *)

Admitted.

(* $ 2 + (1 + n), 2 + (1 + n)
::: $ 2 + n + 1, 2 + n + 1 ::: ⨉ ↕ n_wire (n + 1) $ $ *)
(*  ⨉ ↕ n_wire (1 + n) *)

Lemma cast5 : forall n prf1 prf2 prf3 prf4,
cast (2 + (1 + n)) (2 + (1 + n)) prf1 prf2 
(cast (2 + n + 1) (2 + n + 1) prf3 prf4 
(⨉ ↕ n_wire (n + 1))) ∝ 
(⨉ ↕ n_wire (1 + n)).
Proof.
intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite -> (cast_contract _ _ _ _ _ _ (Stack (Swap) (n_wire ((n) + (1 + 0)%nat)%nat))). (* (cast ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat (Stack (Swap) (nwire ((n) + (1 + 0)%nat)%nat))}) *) (* FROM *) (* (cast ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat (cast (((1 + (1 + 0)%nat)%nat + (n))%nat + (1 + 0)%nat)%nat (((1 + (1 + 0)%nat)%nat + (n))%nat + (1 + 0)%nat)%nat (Stack (Swap) (nwire ((n) + (1 + 0)%nat)%nat))})}) *)
erewrite (cast_stack_distribute _ _ _ _ _ _ (Swap) (n_wire ((n) + (1 + 0)%nat)%nat)). (* (Stack (cast (1 + (1 + 0)%nat)%nat (1 + (1 + 0)%nat)%nat (Swap)}) (cast ((1 + 0)%nat + (n))%nat ((1 + 0)%nat + (n))%nat (nwire ((n) + (1 + 0)%nat)%nat)})) *) (* FROM *) (* (cast ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat ((1 + (1 + 0)%nat)%nat + ((1 + 0)%nat + (n))%nat)%nat (Stack (Swap) (nwire ((n) + (1 + 0)%nat)%nat))}) *)
erewrite (cast_id _ _ (Swap)). (* (Stack (Swap) (cast ((1 + 0)%nat + (n))%nat ((1 + 0)%nat + (n))%nat (nwire ((n) + (1 + 0)%nat)%nat)})) *) (* FROM *) (* (Stack (cast undefined undefined (Swap)}) (cast ((1 + 0)%nat + (n))%nat ((1 + 0)%nat + (n))%nat (nwire ((n) + (1 + 0)%nat)%nat)})) *)
  rewrite -> (cast_n_wire). (* (Stack (Swap) (nwire ((1 + 0)%nat + (n))%nat)) *) (* FROM *) (* (Stack (Swap) (cast ((1 + 0)%nat + (n))%nat ((1 + 0)%nat + (n))%nat (nwire ((n) + (1 + 0)%nat)%nat)})) *)
  reflexivity. (* End ACDC generated solution *)

Admitted.

(* 
$ 1 + (1 + S n), 1 + (1 + S n) ::: — ↕ — ↕ bottom_to_top (S n) $
⟷ ($ 2 + 1 + n, 2 + 1 + n ::: ⨉ ↕ (— ↕ n_wire n) $ ⟷ (— ↕ ⨉ ↕ n_wire n)
   ⟷ $ 2 + 1 + n, 2 + 1 + n ::: ⨉ ↕ (— ↕ n_wire n) $)
⟷ $ 1 + (1 + S n), 1 + (1 + S n) ::: — ↕ — ↕ top_to_bottom_helper n  $*)

(* 
— ↕ — ↕ bottom_to_top (S n)
⟷ (⨉ ↕ (— ↕ n_wire n) ⟷ (— ↕ ⨉ ↕ n_wire n) ⟷ (⨉ ↕ (— ↕ n_wire n)))
⟷ (— ↕ — ↕ top_to_bottom_helper n) *)
Hint Rewrite <- @cast_compose_mid_contract : test_db.
Hint Rewrite @cast_id : test_db.

Lemma test : forall n prf1 prf2 prf3 prf4,

cast (2 + n) (1 + n + 1) prf1 prf2 (— ↕ n_wire (S n))⟷  cast (1 + n + 1) (2 + n) prf3 prf4 ( — ↕n_wire (S n)) ∝ (—  ↕n_wire (S n)) ⟷ (— ↕n_wire (S n)).
Proof.
intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite <- (cast_compose_mid_contract _ _ _ _ _ _ _ _ _ (Stack (Wire) (n_wire (1 + (n))%nat)) (Stack (Wire) (n_wire (1 + (n))%nat))). (* (cast ((1 + (1 + 0)%nat)%nat + (n))%nat ((1 + (1 + 0)%nat)%nat + (n))%nat (Compose (Stack (Wire) (nwire (1 + (n))%nat)) (Stack (Wire) (nwire (1 + (n))%nat)))}) *) (* FROM *) (* (Compose (cast ((1 + (1 + 0)%nat)%nat + (n))%nat (((1 + 0)%nat + (n))%nat + (1 + 0)%nat)%nat (Stack (Wire) (nwire (1 + (n))%nat))}) (cast (((1 + 0)%nat + (n))%nat + (1 + 0)%nat)%nat ((1 + (1 + 0)%nat)%nat + (n))%nat (Stack (Wire) (nwire (1 + (n))%nat))})) *)
  rewrite (cast_id _ _ (Compose (Stack (Wire) (n_wire (1 + (n))%nat)) (Stack (Wire) (n_wire (1 + (n))%nat)))). (* (Compose (Stack (Wire) (nwire (1 + (n))%nat)) (Stack (Wire) (nwire (1 + (n))%nat))) *) (* FROM *) (* (cast undefined undefined (Compose (Stack (Wire) (nwire (1 + (n))%nat)) (Stack (Wire) (nwire (1 + (n))%nat)))}) *)
  reflexivity. (* End ACDC generated solution *)
Admitted.

Lemma cast6 : forall n prf1 prf2 prf3 prf4,
cast (1 + (1 + S n)) (1 + (1 + S n)) prf1 prf2 
(— ↕ — ↕ n_wire (S n)) ⟷ 
cast (2 + 1 + n) (2 + 1 + n) prf3 prf4 
(⨉ ↕ (— ↕ n_wire n)) 
∝ — ↕ — ↕ n_wire (S n)
⟷ (⨉ ↕ (— ↕ n_wire n)).
Proof.
intros.
   idtac "acdc-solution". (* Begin ACDC generated solution *)
   rewrite (cast_id _ _ (Stack (Stack (Wire) (Wire)) (n_wire (1 + (n))%nat))). (* (Compose (Stack (Stack (Wire) (Wire)) (nwire (1 + (n))%nat)) (cast (((1 + (1 + 0)%nat)%nat + (1 + 0)%nat)%nat + (n))%nat (((1 + (1 + 0)%nat)%nat + (1 + 0)%nat)%nat + (n))%nat (Stack (Swap) (Stack (Wire) (nwire (n))))})) *) (* FROM *) (* (Compose (cast undefined undefined (Stack (Stack (Wire) (Wire)) (nwire (1 + (n))%nat))}) (cast (((1 + (1 + 0)%nat)%nat + (1 + 0)%nat)%nat + (n))%nat (((1 + (1 + 0)%nat)%nat + (1 + 0)%nat)%nat + (n))%nat (Stack (Swap) (Stack (Wire) (nwire (n))))})) *)
 rewrite (cast_id _ _ (Stack (Swap) (Stack (Wire) (n_wire (n))))). (* (Compose (Stack (Stack (Wire) (Wire)) (nwire (1 + (n))%nat)) (Stack (Swap) (Stack (Wire) (nwire (n))))) *) (* FROM *) (* (Compose (Stack (Stack (Wire) (Wire)) (nwire (1 + (n))%nat)) (cast undefined undefined (Stack (Swap) (Stack (Wire) (nwire (n))))})) *)
   reflexivity. (* End ACDC generated solution *)
Admitted.


(* $ output + bot, top + S (mid + bot)
::: Z output (top + S mid) β ↕ ZXCore.transpose (n_wire bot) $
⟷ (n_wire top ↕ Z (S (mid + bot)) input α) *)
(* Z output (top + S mid) β ↕ ZXCore.transpose (n_wire bot)
⟷ $ top + S mid + bot, top + input
  ::: n_wire top ↕ Z (S (mid + bot)) input α $ *)
Lemma cast8 : forall top mid bot input output α β prf1 prf2 prf3 prf4,
cast (output + bot) (top + S (mid + bot)) prf1 prf2
(Z output (top + S mid) β ↕ (n_wire bot)) ⟷
(n_wire top ↕ Z (S (mid + bot)) input α) ∝
Z output (top + S mid) β ↕ (n_wire bot) ⟷
cast (top + S mid + bot) (top + input) prf3 prf4
(n_wire top ↕ Z (S (mid + bot)) input α).
Proof.
intros.

  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite (cast_compose_l _ _ (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (n_wire (bot))) (Stack (n_wire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))). (* (cast ((output) + (bot))%nat undefined (Compose (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (nwire (bot))) (cast undefined undefined (Stack (nwire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))}))}) *) (* FROM *) (* (Compose (cast ((output) + (bot))%nat undefined (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (nwire (bot)))}) (Stack (nwire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))) *)
rewrite (cast_id _ _ (Compose (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (n_wire (bot))) (cast (((top) + (1 + (mid))%nat)%nat + (bot))%nat ((top) + (input))%nat _ _ (Stack (n_wire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))))). (* (Compose (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (nwire (bot))) (cast (((top) + (1 + (mid))%nat)%nat + (bot))%nat ((top) + (input))%nat (Stack (nwire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))})) *) (* FROM *) (* (cast undefined undefined (Compose (Stack (Z (output) ((top) + (1 + (mid))%nat)%nat (β)) (nwire (bot))) (cast (((top) + (1 + (mid))%nat)%nat + (bot))%nat ((top) + (input))%nat (Stack (nwire (top)) (Z (1 + ((mid) + (bot))%nat)%nat (input) (α)))}))}) *)
  (* reflexivity. End ACDC generated solution *)
Admitted.

(* $ n + 0, m + 1
  ::: $ n, n + 1 + 1 ::: n_wire n ↕ ⊂ $
      ⟷ $ n + 1 + 1, 3 ::: Z n 1 0 ↕ (— ↕ —) $ ⟷ (Z 2 m α ↕ —) $*)
(* $ n + 0, m + 1::: n_wire n ↕ ⊂ ⟷ (Z n 1 0 ↕ (— ↕ —)) ⟷ (Z 2 m α ↕ —) $*)
Lemma cast9 : forall n m α prf1 prf2 prf3 prf4 prf5 prf6 prf7 prf8,
cast (n + 0) (m + 1) prf1 prf2
(cast (n) (n + 1 + 1) prf3 prf4
(n_wire n ↕ ⊂) ⟷
cast (n + 1 + 1) 3 prf5 prf6
(Z n 1 0 ↕ (— ↕ —)) ⟷ (Z 2 m α ↕ —)) ∝
cast (n + 0) (m + 1) prf7 prf8 (n_wire n ↕ ⊂ ⟷ (Z n 1 0 ↕ (— ↕ —)) ⟷ (Z 2 m α ↕ —)).
Proof. (* TODO: Debug *)
intros.



Admitted.

Lemma cast7 : forall m α prf1 prf2 ,
cast (1 + (1 + 0) + 1)  (m + 1) prf1 prf2 (Z (1 + (1 + 0)) m α ↕ —) ∝   Z 2 m α ↕ —.
Proof.
intros.
  idtac "acdc-solution". (* Begin ACDC generated solution *)
  erewrite <- (cast_stack_l _ _ _ _ (Z ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (α)) (Wire)). (* (Stack (cast ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (Z ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (α))}) (Wire)) *) (* FROM *) (* (cast (((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat + undefined)%nat ((m) + undefined)%nat (Stack (Z ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (α)) (Wire))}) *)
  rewrite -> (cast_Z). (* (Stack (Z ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (α)) (Wire)) *) (* FROM *) (* (Stack (cast ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (Z ((1 + 0)%nat + ((1 + 0)%nat + 0)%nat)%nat (m) (α))}) (Wire)) *)
  reflexivity. (* End ACDC generated solution *)
Admitted.

