Require Import CoreData.

(* Various computational results about explicit ZX-diagrams *)

Local Open Scope matrix_scope.

Lemma X_0_0_semantics (r : R) : 
  ⟦ X 0 0 r ⟧ = (1 + Cexp r) .* I 1. 
Proof.
  lma'.
Qed.

Lemma Z_0_0_semantics (r : R) : 
  ⟦ Z 0 0 r ⟧ = (1 + Cexp r) .* I 1. 
Proof.
  lma'.
Qed.

Lemma Z_semantics_0_0' (r : R) : 
  Z_semantics 0 0 r = (1 + Cexp r) .* I 1. 
Proof.
  exact (Z_0_0_semantics r).
Qed.


Lemma Z_0_2_semantics α : 
  Z_semantics 0 2 α = make_WF (list2D_to_matrix [[C1];[C0];[C0];[Cexp α]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; reflexivity.
Qed.

Lemma X_2_1_0_semantics : X_semantics 2 1 0 = 
  make_WF (list2D_to_matrix [[/√2;C0;C0;/√2];[C0;/√2;/√2;C0]]).
Proof.
  rewrite X_semantics_equiv.
  cbn.
  rewrite 4 kron_1_l, Cexp_0, Mscale_1_l by auto_wf.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  unfold xbasis_plus, xbasis_minus, braplus, braminus;
    autounfold with U_db; cbn; by_cell_no_intros; cbn;
    Csimpl; group_radicals; C_field; lca.
Qed.

Lemma Z_4_1_0_semantics : Z_semantics 4 1 0 = make_WF
  (list2D_to_matrix
     [[C1;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0];
      [C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;C0;
       C1]]).
Proof.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; [reflexivity..|].
  rewrite Cexp_0.
  reflexivity.
Qed.


Lemma zx_triangle_semantics_alt : ⟦ ▷ ⟧ = 
  make_WF (list2D_to_matrix [[C1;C0];[C1;C1]]).
Proof.
  rewrite zx_triangle_semantics.
  prep_matrix_equivalence.
  rewrite make_WF_equiv.
  by_cell; autounfold with U_db; cbn; lca.
Qed.

Lemma zx_left_triangle_semantics_alt : ⟦ ◁ ⟧ = 
  make_WF (list2D_to_matrix [[C1;C1];[C0;C1]]).
Proof.
  change zx_triangle_left with (▷ ⊤%ZX).
  rewrite semantics_transpose_comm.
  rewrite zx_triangle_semantics_alt.
  prep_matrix_equivalence.
  by_cell; reflexivity.
Qed.