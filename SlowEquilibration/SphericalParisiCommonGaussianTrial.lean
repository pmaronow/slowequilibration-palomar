-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGaussianREMJensen
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! True independent common/fresh Gaussian trial endpoint. Joint
integrability follows from the actual conditional iid-row bound and its
integrable common squared-norm envelope, before genuine product Fubini. -/

namespace SlowEquilibration.SphericalParisiCommonGaussianTrial
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalParisiGaussianREMJensen
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def commonRowLogAverage {N k : ℕ} (a0 a ell : ℝ)
    (p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin k × Fin N)) : ℝ :=
  actualGaussianNormLogAverage (Real.sqrt a0 • p.1) a ell p.2

def commonRowLaw (N k : ℕ) := (stdGaussian (EuclideanSpace ℝ (Fin N))).prod
  (SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N))

theorem commonRowLogAverage_measurable (N k : ℕ) (a0 a ell : ℝ) :
    Measurable (commonRowLogAverage (N := N) (k := k) a0 a ell) := by
  unfold commonRowLogAverage actualGaussianNormLogAverage logAverageExp
  apply Measurable.log
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  apply Measurable.exp
  apply measurable_const.mul
  exact ((measurable_fst.const_smul (Real.sqrt a0)).add
    (((projectGaussian_measurable (fun j : Fin N => (i,j))).comp measurable_snd).const_smul (Real.sqrt a))).norm

theorem commonRowLogAverage_nonnegative {N k : ℕ} (hk : 0 < k)
    (a0 a : ℝ) {ell : ℝ} (hEll : 0 ≤ ell)
    (p : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin k × Fin N)) :
    0 ≤ commonRowLogAverage a0 a ell p :=
  logAverageExp_nonnegative k hk _ (fun _i => mul_nonneg hEll (norm_nonneg _))

private theorem conditional_row_bound {N k : ℕ} (hk : 0 < k)
    {a0 a ell m b : ℝ} (ha0 : 0 ≤ a0) (ha : 0 ≤ a) (hEll : 0 ≤ ell)
    (hm : 0 < m) (hm1 : m ≤ 1) (hb : 0 < b) (hmargin : 0 < b-(m*ell)*a)
    (g0 : EuclideanSpace ℝ (Fin N)) :
    (∫ g,commonRowLogAverage a0 a ell (g0,g)
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)) ≤
      -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2+
        (ell*a0/(2*(b-(m*ell)*a)))*‖g0‖^2+(1-m)*Real.log (k : ℝ)/m := by
  have H := actual_gaussian_norm_log_average_quadratic_upper hk (Real.sqrt a0 • g0)
    ha hEll hm hm1 hb hmargin
  apply H.trans_eq
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt ha0]
  ring

/-- Actual joint common/fresh Gaussian integrability, with neither
integrability nor the desired trial bound supplied as a hypothesis. -/
theorem actual_common_row_integrable {N k : ℕ} (hk : 0 < k)
    {a0 a ell m b : ℝ} (ha0 : 0 ≤ a0) (ha : 0 ≤ a) (hEll : 0 ≤ ell)
    (hm : 0 < m) (hm1 : m ≤ 1) (hb : 0 < b) (hmargin : 0 < b-(m*ell)*a) :
    Integrable (commonRowLogAverage (N := N) (k := k) a0 a ell) (commonRowLaw N k) := by
  let μ := stdGaussian (EuclideanSpace ℝ (Fin N))
  let ν := SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)
  let F := commonRowLogAverage (N := N) (k := k) a0 a ell
  let H := fun g0 : EuclideanSpace ℝ (Fin N) =>
    -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2+
      (ell*a0/(2*(b-(m*ell)*a)))*‖g0‖^2+(1-m)*Real.log (k : ℝ)/m
  have hiH : Integrable H μ :=
    ((integrable_const _).add ((IsGaussian.memLp_two_id (μ := μ)).norm.integrable_sq.const_mul _)).add
      (integrable_const _)
  have hF : Measurable F := commonRowLogAverage_measurable N k a0 a ell
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  refine ⟨.of_forall fun g0 =>
    (actual_gaussian_norm_log_average_upper hk (Real.sqrt a0 • g0) ha hEll hm hm1 hb hmargin).1,?_⟩
  have hmF := hF.stronglyMeasurable.norm.integral_prod_right' (ν := ν)
  apply hiH.mono' hmF.aestronglyMeasurable
  exact .of_forall fun g0 => by
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    have he : (∫ g,‖F (g0,g)‖ ∂ν)=(∫ g,F (g0,g) ∂ν) := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        dsimp only
        rw [Real.norm_eq_abs,abs_of_nonneg (commonRowLogAverage_nonnegative hk a0 a hEll (g0,g))]
    rw [he]
    exact conditional_row_bound hk ha0 ha hEll hm hm1 hb hmargin g0

/-- True averaged determinant/common-field trial. The common squared-norm
term is evaluated by the literal standard Gaussian second momentN. -/
theorem actual_common_row_quadratic_upper {N k : ℕ} (hk : 0 < k)
    {a0 a ell m b : ℝ} (ha0 : 0 ≤ a0) (ha : 0 ≤ a) (hEll : 0 ≤ ell)
    (hm : 0 < m) (hm1 : m ≤ 1) (hb : 0 < b) (hmargin : 0 < b-(m*ell)*a) :
    (∫ p,commonRowLogAverage (N := N) (k := k) a0 a ell p ∂commonRowLaw N k) ≤
      -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2+
        ell*a0*(N : ℝ)/(2*(b-(m*ell)*a))+(1-m)*Real.log (k : ℝ)/m := by
  have hi := actual_common_row_integrable (N := N) hk ha0 ha hEll hm hm1 hb hmargin
  let μ := stdGaussian (EuclideanSpace ℝ (Fin N))
  let ν := SYK.standardGaussianMeasureOnEuclidean (Fin k × Fin N)
  let H := fun g0 : EuclideanSpace ℝ (Fin N) =>
    -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2+
      (ell*a0/(2*(b-(m*ell)*a)))*‖g0‖^2+(1-m)*Real.log (k : ℝ)/m
  have hsq : Integrable (fun g0 : EuclideanSpace ℝ (Fin N) => ‖g0‖^2) μ :=
    (IsGaussian.memLp_two_id (μ := μ)).norm.integrable_sq
  have hiH : Integrable H μ := ((integrable_const _).add (hsq.const_mul _)).add (integrable_const _)
  unfold commonRowLaw at hi ⊢
  rw [integral_prod _ hi]
  have HB := integral_mono hi.integral_prod_left hiH (conditional_row_bound hk ha0 ha hEll hm hm1 hb hmargin)
  apply HB.trans_eq
  change (∫ g0,H g0 ∂μ)=_
  unfold H
  rw [integral_add
    (f := fun g0 : EuclideanSpace ℝ (Fin N) =>
      -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2+
        (ell*a0/(2*(b-(m*ell)*a)))*‖g0‖^2)
    (g := fun _ => (1-m)*Real.log (k : ℝ)/m)
    ((integrable_const _).add (hsq.const_mul _)) (integrable_const _),
    integral_add
      (f := fun _ : EuclideanSpace ℝ (Fin N) => -((N : ℝ)/2)*Real.log (1-(m*ell)*a/b)/m+ell*b/2)
      (g := fun g0 => (ell*a0/(2*(b-(m*ell)*a)))*‖g0‖^2)
      (integrable_const _) (hsq.const_mul _),
    integral_const_mul (ell*a0/(2*(b-(m*ell)*a))) (fun g0 : EuclideanSpace ℝ (Fin N) => ‖g0‖^2)]
  simp only [integral_const,probReal_univ,one_smul]
  rw [GaussianNormMean.integral_norm_sq_stdGaussian,finrank_euclideanSpace,Fintype.card_fin]
  ring

end
end SlowEquilibration.SphericalParisiCommonGaussianTrial
