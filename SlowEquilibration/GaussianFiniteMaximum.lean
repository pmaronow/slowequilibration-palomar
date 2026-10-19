-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianIncrementComparison
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Order.Lattice

/-! Finite Gaussian maximum comparison obtained from the proved ordinary
Gaussian log-partition interpolation. The zero-temperature limit is controlled
by the deterministic log-cardinality error. -/

@[expose] public section
namespace SlowEquilibration.GaussianFiniteMaximum
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open GaussianSpinComparison GaussianSpinInterpolation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type*} [Fintype V] [Nonempty V]

def maximum (f : V → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty f

lemma le_maximum (f : V → ℝ) (v : V) : f v ≤ maximum f :=
  Finset.le_sup' f (Finset.mem_univ v)

lemma maximum_le (f : V → ℝ) {c : ℝ} (h : ∀ v, f v ≤ c) : maximum f ≤ c :=
  Finset.sup'_le _ _ (fun v _ => h v)

lemma maximum_attained (f : V → ℝ) : ∃ v, maximum f = f v := by
  obtain ⟨v, _, hv⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  exact ⟨v, hv⟩

lemma log_mean_exp_bounds (f : V → ℝ) {β : ℝ} (hβ : 0 < β) :
    β * maximum f - Real.log (Fintype.card V) ≤
      Real.log ((∑ v, Real.exp (β * f v)) / Fintype.card V) ∧
    Real.log ((∑ v, Real.exp (β * f v)) / Fintype.card V) ≤ β * maximum f := by
  have hc : (0 : ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨v, hv⟩ := maximum_attained f
  have hs : Real.exp (β * maximum f) ≤ ∑ v, Real.exp (β * f v) := by
    rw [hv]
    exact Finset.single_le_sum (f := fun i => Real.exp (β * f i)) (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ v)
  have hu : (∑ v, Real.exp (β * f v)) ≤ Fintype.card V * Real.exp (β * maximum f) := by
    calc
      _ ≤ ∑ _v : V, Real.exp (β * maximum f) :=
        Finset.sum_le_sum (fun v _ => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_maximum f v) hβ.le))
      _ = _ := by simp
  have hsp : 0 < (∑ v, Real.exp (β * f v)) / (Fintype.card V : ℝ) :=
    div_pos ((Real.exp_pos _).trans_le hs) hc
  constructor
  · have h := Real.log_le_log (div_pos (Real.exp_pos _) hc) (div_le_div_of_nonneg_right hs hc.le)
    rw [Real.log_div (Real.exp_pos _).ne' hc.ne', Real.log_exp] at h
    exact h
  · have hu' : (∑ v, Real.exp (β * f v)) / (Fintype.card V : ℝ) ≤ Real.exp (β * maximum f) :=
      (div_le_iff₀ hc).mpr (by simpa only [mul_comm] using hu)
    have h := Real.log_le_log hsp hu'
    simpa only [Real.log_exp] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma maximum_rotated_integrable (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ v, ‖L v‖ ≤ K) (label : ι → Bool) (θ : ℝ) :
    Integrable (fun w => maximum (fun v => L v (rotation label θ w)))
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  have hc : Continuous (fun w => maximum (fun v => L v (rotation label θ w))) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty (fun v _ => (L v).continuous.comp (rotation label θ).continuous)
  apply (gaussian_norm_integrable.const_mul K).mono' hc.aestronglyMeasurable
  exact .of_forall fun w => by
    obtain ⟨v, hv⟩ := maximum_attained (fun v => L v (rotation label θ w))
    rw [hv]
    exact (L v).le_opNorm _ |>.trans ((mul_le_mul_of_nonneg_right (hb v) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (rotation_norm_le label θ w) hK))

lemma signedKernel_smul (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (β : ℝ) (v u : V) :
    signedKernel (fun v => β • L v) label v u = β ^ 2 * signedKernel L label v u := by
  simp only [signedKernel, coordinateObservable, smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring


variable [MeasurableSpace V] [MeasurableSingletonClass V]

lemma finite_logPartition_eq (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (β : ℝ) (w : EuclideanSpace ℝ ι) :
    logPartition (PMF.uniformOfFintype V).toMeasure (fun v => β • L v) w =
      Real.log ((∑ v, Real.exp (β * L v w)) / Fintype.card V) := by
  unfold logPartition GaussianSpinInterpolation.moment
  rw [PMF.integral_eq_sum]
  congr 1
  simp only [weight, one_mul, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, smul_apply]
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- Sudakov–Fernique comparison for the actual finite Gaussian fields. No
pointwise variance equality is assumed: the hypothesis compares increments. -/
theorem expected_maximum_comparison (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool)
    (hinc : ∀ v u, 0 ≤ signedKernel L label v v + signedKernel L label u u -
      2 * signedKernel L label v u) :
    (∫ w, maximum (fun v => L v (rotation label 0 w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
    ∫ w, maximum (fun v => L v (rotation label (Real.pi / 2) w))
      ∂SYK.standardGaussianMeasureOnEuclidean ι := by
  let ν := (PMF.uniformOfFintype V).toMeasure
  let K : ℝ := ∑ v, ‖L v‖
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ v, ‖L v‖ ≤ K := fun v =>
    Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
  have hi (θ : ℝ) := maximum_rotated_integrable L hK hb label θ
  have hc : (0 : ℝ) ≤ Real.log (Fintype.card V) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos (α := V))
  apply le_of_forall_pos_le_add
  intro ε hε
  let β : ℝ := (Real.log (Fintype.card V) + 1) / ε
  have hβ : 0 < β := div_pos (by linarith) hε
  have hβeq : β * ε = Real.log (Fintype.card V) + 1 := by
    dsimp [β]
    exact div_mul_cancel₀ _ hε.ne'
  have hbβ : ∀ᵐ v ∂ν, ‖β • L v‖ ≤ β * K := .of_forall fun v => by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hβ]
    exact mul_le_mul_of_nonneg_left (hb v) hβ.le
  have hilp (θ : ℝ) := logPartition_rotated_gaussian_integrable ν
    (fun v => β • L v) (measurable_of_finite _) (mul_nonneg hβ.le hK) hbβ label θ
  have hcomp := gaussian_increment_comparison ν (fun v => β • L v)
    (measurable_of_finite _) (mul_nonneg hβ.le hK) hbβ label (Filter.Eventually.of_forall fun z => by
      rw [signedKernel_smul, signedKernel_smul, signedKernel_smul]
      nlinarith [mul_nonneg (sq_nonneg β) (hinc z.1 z.2)])
  have hilow : Integrable (fun w => β * maximum (fun v => L v (rotation label 0 w)) -
      Real.log (Fintype.card V)) (SYK.standardGaussianMeasureOnEuclidean ι) := by
    exact ((hi 0).const_mul β).sub (integrable_const _)
  have hlo := integral_mono hilow (hilp 0) (fun w => by
      change _ ≤ logPartition (PMF.uniformOfFintype V).toMeasure _ _
      rw [finite_logPartition_eq]
      exact (log_mean_exp_bounds (fun v => L v (rotation label 0 w)) hβ).1)
  have hup := integral_mono (hilp (Real.pi / 2)) ((hi (Real.pi / 2)).const_mul β)
    (fun w => by
      change logPartition (PMF.uniformOfFintype V).toMeasure _ _ ≤ _
      rw [finite_logPartition_eq]
      exact (log_mean_exp_bounds (fun v => L v (rotation label (Real.pi / 2) w)) hβ).2)
  rw [integral_sub ((hi 0).const_mul β) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hlo
  rw [integral_const_mul] at hup
  unfold averagedRotatedLogPartition at hcomp
  have h := hlo.trans (hcomp.trans hup)
  nlinarith

end
end SlowEquilibration.GaussianFiniteMaximum
