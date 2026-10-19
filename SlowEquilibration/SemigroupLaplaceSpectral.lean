-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemigroupLaplaceShift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-!
# Recovering semigroup multipliers from its actual Laplace operator

A Laplace eigenvector is shown to solve the actual semigroup evolution ODE.
The resulting multiplier is derived, rather than supplied in a diagonal
operator definition. Any genuine eigen-Hilbert basis therefore gives the
physical operator's convergent spectral expansion.
-/

namespace SlowEquilibration.SemigroupLaplace.Data
noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : SlowEquilibration.SemigroupLaplace.Data E)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem P_hasDerivAt_of_laplace_eigen {v : E} {μ : ℝ} (hμ : μ ≠ 0)
    (he : S.operator v = μ • v) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => S.P s.toNNReal v)
      (-(μ⁻¹ - 1) • S.P t.toNNReal v) t := by
  have hRy : S.operator (μ⁻¹ • v) = v := by
    rw [map_smul, he, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hd := S.P_operator_hasDerivAt ht (μ⁻¹ • v)
  rw [hRy] at hd
  apply hd.congr_deriv
  rw [map_smul]
  calc
    _ = (1 - μ⁻¹) • S.P t.toNNReal v := by rw [sub_smul, one_smul]
    _ = _ := by congr 1; ring

theorem P_laplace_eigen {v : E} {μ : ℝ} (hμ : μ ≠ 0)
    (he : S.operator v = μ • v) (t : ℝ≥0) :
    S.P t v = Real.exp (-(t : ℝ) * (μ⁻¹ - 1)) • v := by
  let ell := μ⁻¹ - 1
  let F : ℝ → E := fun s => Real.exp (ell * s) • S.P s.toNNReal v
  have hF : Continuous F :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
      ((S.continuous v).comp continuous_real_toNNReal)
  have hdF (s : ℝ) (hs : 0 < s) : HasDerivAt F 0 s := by
    have hdexp := (Real.hasDerivAt_exp (ell * s)).comp s ((hasDerivAt_id s).const_mul ell)
    have hd := hdexp.smul (S.P_hasDerivAt_of_laplace_eigen hμ he hs)
    apply hd.congr_deriv
    dsimp [ell]
    rw [smul_smul]
    module
  have hconst : ∀ s ∈ Ioi (0 : ℝ), F s = F 1 := by
    intro s hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun u hu => (hdF u hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (hdF u hu).deriv) hs (by norm_num)
  have hclosed : IsClosed {s : ℝ | F s = F 1} := isClosed_eq hF continuous_const
  have hzero : F 0 = F 1 :=
    (closure_minimal hconst hclosed) (show (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) by
      rw [closure_Ioi]; exact self_mem_Ici)
  have hzero' : F 0 = v := by simp [F, S.zero]
  by_cases ht : t = 0
  · simp [ht, S.zero]
  have ht0 : 0 < (t : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr ht
  have htv : Real.exp (ell * (t : ℝ)) • S.P t v = v := by
    have hc := (hconst (t : ℝ) ht0).trans (hzero.symm.trans hzero')
    simpa only [F, Real.toNNReal_coe] using hc
  have h := congrArg (fun w : E => Real.exp (-ell * (t : ℝ)) • w) htv
  rw [smul_smul, ← Real.exp_add] at h
  have hcancel : -ell * (t : ℝ) + ell * (t : ℝ) = 0 := by ring
  rw [hcancel, Real.exp_zero, one_smul] at h
  convert h using 1
  congr 2
  dsimp [ell]
  ring

end

section Hilbert
open scoped NNReal InnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (S : SlowEquilibration.SemigroupLaplace.Data H)

theorem P_hasSum_eigenbasis {ι : Type*} (b : HilbertBasis ι ℝ H) (μ : ι → ℝ)
    (hμ : ∀ i, μ i ≠ 0) (he : ∀ i, S.operator (b i) = μ i • b i)
    (t : ℝ≥0) (f : H) :
    HasSum (fun i => (Real.exp (-(t : ℝ) * ((μ i)⁻¹ - 1)) * inner ℝ (b i) f) • b i)
      (S.P t f) := by
  have h := (b.hasSum_repr f).mapL (S.P t)
  simpa only [map_smul, S.P_laplace_eigen (hμ _) (he _),
    HilbertBasis.repr_apply_apply, smul_smul, mul_comm] using h

end Hilbert
end SlowEquilibration.SemigroupLaplace.Data
