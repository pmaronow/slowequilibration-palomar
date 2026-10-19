-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! Genuine finite symmetric spectral scaling, with every eigenvalue
multiplicity retained, proved by the actual characteristic polynomial. -/
@[expose] public section
namespace SlowEquilibration.SymmetricSpectralScale
noncomputable section
open Function Module Polynomial
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma symmetric_smul (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (a : ℝ) :
    (a • T).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (a • T x) y=inner ℝ x (a • T y)
  rw [real_inner_smul_left,real_inner_smul_right]
  exact congrArg (fun z:ℝ=>a*z) (hT x y)

/-- Actual finite eigenvalue sums scale with the operator, including
negative scalars and zero dimension; no spectral scaling premise. -/
theorem spectral_sum_smul (T : E →L[ℝ] E) (hT : T.toLinearMap.IsSymmetric) (a : ℝ) (f : ℝ → ℝ) :
    (∑ i : Fin (Module.finrank ℝ E),f ((symmetric_smul T hT a).eigenvalues rfl i))=
      ∑ i : Fin (Module.finrank ℝ E),f (a*hT.eigenvalues rfl i) := by
  classical
  let S:=a • T
  let B:=hT.eigenvectorBasis (show Module.finrank ℝ E=Module.finrank ℝ E from rfl)
  have hmat : S.toLinearMap.toMatrix B.toBasis B.toBasis=
      Matrix.diagonal (fun i=>a*hT.eigenvalues rfl i) := by
    change LinearMap.toMatrix B.toBasis B.toBasis (a • T.toLinearMap)=_
    rw [map_smul]
    have hold : T.toLinearMap.toMatrix B.toBasis B.toBasis=Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues rfl) :=
      hT.toMatrix_eigenvectorBasis rfl
    rw [hold]
    ext i j
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.diagonal_apply,RCLike.ofReal_real_eq_id,id_eq,Function.comp_def]
    split_ifs <;> ring
  have hroots : S.toLinearMap.charpoly.roots=
      Multiset.map (fun i:Fin (Module.finrank ℝ E)=>a*hT.eigenvalues rfl i) Finset.univ.val := by
    rw [← S.toLinearMap.charpoly_toMatrix B.toBasis,hmat,Matrix.charpoly_diagonal,
      Polynomial.roots_prod _ _ (by
        apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        exact Polynomial.X_sub_C_ne_zero _)]
    simp only [Polynomial.roots_X_sub_C,Multiset.bind_singleton]
  have hrootsS:=(symmetric_smul T hT a).roots_charpoly_eq_eigenvalues rfl
  change S.toLinearMap.charpoly.roots=_ at hrootsS
  rw [hroots] at hrootsS
  have hh:=congrArg (fun m:Multiset ℝ=>(m.map f).sum) hrootsS
  simpa only [Multiset.map_map,Function.comp_def,RCLike.ofReal_real_eq_id,id_eq,Finset.sum] using hh.symm

end
end SlowEquilibration.SymmetricSpectralScale
