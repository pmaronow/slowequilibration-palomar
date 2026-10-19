module
public import FRSB.ConstantMassEvolution
public import Paper.HJBVerification
public import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

@[expose] public section

/-! Bounded backward Gaussian quotient tests used to identify the actual
constant-mass state law. The analytic heat functions below use actual
Gaussian integrals. -/

noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ContDiff
namespace FRSB
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory

structure HeatC2Datum (F : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ 2 F
  growth : ∀ j ≤ 2, HasExpGrowth (iteratedDeriv j F)

def gaussianHeatFlow (F : ℝ → ℝ) (v x : ℝ) : ℝ :=
  ∫ z, F (x + z) ∂gaussianReal 0 v.toNNReal

theorem continuous_gaussianHeatFlow {F : ℝ → ℝ} (hF : HeatC2Datum F) :
    Continuous (fun p : ℝ × ℝ => gaussianHeatFlow F p.1 p.2) := by
  have h := continuous_integral_comp_add_gaussianReal hF.smooth.continuous
    (by simpa only [iteratedDeriv_zero] using hF.growth 0 (by norm_num))
  exact h.comp continuous_swap

theorem contDiff_gaussianHeatFlow_spatial {F : ℝ → ℝ} (hF : HeatC2Datum F) (v : ℝ) :
    ContDiff ℝ 2 (gaussianHeatFlow F v) :=
  contDiff_integral_comp_add_gaussianReal hF.smooth hF.growth v.toNNReal

theorem iteratedDeriv_gaussianHeatFlow {F : ℝ → ℝ} (hF : HeatC2Datum F)
    (v : ℝ) {j : ℕ} (hj : j ≤ 2) :
    iteratedDeriv j (gaussianHeatFlow F v) = gaussianHeatFlow (iteratedDeriv j F) v :=
  iteratedDeriv_integral_comp_add_gaussianReal hF.smooth hF.growth v.toNNReal hj

theorem hasDerivAt_gaussianHeatFlow_spatial {F : ℝ → ℝ} (hF : HeatC2Datum F)
    (v x : ℝ) : HasDerivAt (gaussianHeatFlow F v) (gaussianHeatFlow (deriv F) v x) x := by
  have hd := ((contDiff_gaussianHeatFlow_spatial hF v).differentiable (by norm_num) x).hasDerivAt
  have he := iteratedDeriv_gaussianHeatFlow hF v (j := 1) (by norm_num)
  simp only [iteratedDeriv_one] at he
  simpa only [he] using hd

theorem hasDerivAt_gaussianHeatFlow_first_spatial {F : ℝ → ℝ} (hF : HeatC2Datum F)
    (v x : ℝ) : HasDerivAt (gaussianHeatFlow (deriv F) v)
      (gaussianHeatFlow (iteratedDeriv 2 F) v x) x := by
  have hd := ((contDiff_gaussianHeatFlow_spatial hF v).differentiable_iteratedDeriv
    1 (by norm_num) x).hasDerivAt
  have he1 := iteratedDeriv_gaussianHeatFlow hF v (j := 1) (by norm_num)
  have he2 := iteratedDeriv_gaussianHeatFlow hF v (j := 2) (by norm_num)
  simp only [iteratedDeriv_one] at he1
  rw [← iteratedDeriv_succ] at hd
  change HasDerivAt (iteratedDeriv 1 (gaussianHeatFlow F v))
    (iteratedDeriv 2 (gaussianHeatFlow F v) x) x at hd
  simpa only [iteratedDeriv_one, he1, he2] using hd

theorem hasDerivAt_gaussianHeatFlow_variance {F : ℝ → ℝ} (hF : HeatC2Datum F)
    {v : ℝ} (hv : 0 < v) (x : ℝ) :
    HasDerivAt (fun w => gaussianHeatFlow F w x)
      ((1 / 2 : ℝ) * gaussianHeatFlow (iteratedDeriv 2 F) v x) v := by
  have hd := hasDerivAt_iteratedDeriv_integral_comp_add_gaussianReal_var
    hF.smooth hF.growth (i := 0) (by norm_num) hv x
  change HasDerivAt (fun w => gaussianHeatFlow F w x)
    ((1 / 2 : ℝ) * iteratedDeriv 2 (gaussianHeatFlow F v) x) v at hd
  rw [iteratedDeriv_gaussianHeatFlow hF v (j := 2) (by norm_num)] at hd
  exact hd

theorem continuous_gaussianHeatFlow_jet {F : ℝ → ℝ} (hF : HeatC2Datum F)
    {j : ℕ} (hj : j ≤ 2) :
    Continuous (fun p : ℝ × ℝ => gaussianHeatFlow (iteratedDeriv j F) p.1 p.2) := by
  have h := continuous_integral_comp_add_gaussianReal
    (hF.smooth.continuous_iteratedDeriv j (by exact_mod_cast hj)) (hF.growth j hj)
  exact h.comp continuous_swap

def backwardHeatQuotient (N D : ℝ → ℝ) (v x : ℝ) : ℝ :=
  gaussianHeatFlow N v x / gaussianHeatFlow D v x

def backwardHeatQuotientDx (N D : ℝ → ℝ) (v x : ℝ) : ℝ :=
  (gaussianHeatFlow (deriv N) v x * gaussianHeatFlow D v x -
    gaussianHeatFlow N v x * gaussianHeatFlow (deriv D) v x) / gaussianHeatFlow D v x ^ 2

def backwardHeatQuotientDxx (N D : ℝ → ℝ) (v x : ℝ) : ℝ :=
  ((gaussianHeatFlow (iteratedDeriv 2 N) v x * gaussianHeatFlow D v x -
      gaussianHeatFlow N v x * gaussianHeatFlow (iteratedDeriv 2 D) v x) *
        gaussianHeatFlow D v x ^ 2 -
    (gaussianHeatFlow (deriv N) v x * gaussianHeatFlow D v x -
      gaussianHeatFlow N v x * gaussianHeatFlow (deriv D) v x) *
        (2 * gaussianHeatFlow D v x * gaussianHeatFlow (deriv D) v x)) /
          (gaussianHeatFlow D v x ^ 2) ^ 2

def backwardHeatQuotientDv (N D : ℝ → ℝ) (v x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * gaussianHeatFlow (iteratedDeriv 2 N) v x * gaussianHeatFlow D v x -
    gaussianHeatFlow N v x * ((1 / 2 : ℝ) * gaussianHeatFlow (iteratedDeriv 2 D) v x)) /
      gaussianHeatFlow D v x ^ 2

theorem hasDerivAt_backwardHeatQuotient_spatial {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D) (v x : ℝ)
    (hpos : gaussianHeatFlow D v x ≠ 0) :
    HasDerivAt (backwardHeatQuotient N D v) (backwardHeatQuotientDx N D v x) x :=
  (hasDerivAt_gaussianHeatFlow_spatial hN v x).div
    (hasDerivAt_gaussianHeatFlow_spatial hD v x) hpos

theorem hasDerivAt_backwardHeatQuotientDx {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D) (v x : ℝ)
    (hpos : gaussianHeatFlow D v x ≠ 0) :
    HasDerivAt (backwardHeatQuotientDx N D v) (backwardHeatQuotientDxx N D v x) x := by
  have hn0 := hasDerivAt_gaussianHeatFlow_spatial hN v x
  have hd0 := hasDerivAt_gaussianHeatFlow_spatial hD v x
  have hn1 := hasDerivAt_gaussianHeatFlow_first_spatial hN v x
  have hd1 := hasDerivAt_gaussianHeatFlow_first_spatial hD v x
  have hh := ((hn1.mul hd0).sub (hn0.mul hd1)).div (hd0.pow 2) (pow_ne_zero 2 hpos)
  convert hh using 1
  · rfl
  · unfold backwardHeatQuotientDxx
    simp only [Pi.pow_apply, Pi.sub_apply, Pi.mul_apply] at *
    congr 1
    ring

theorem hasDerivAt_backwardHeatQuotient_variance {N D : ℝ → ℝ}
    (hN : HeatC2Datum N) (hD : HeatC2Datum D) {v : ℝ} (hv : 0 < v) (x : ℝ)
    (hpos : gaussianHeatFlow D v x ≠ 0) :
    HasDerivAt (fun w => backwardHeatQuotient N D w x) (backwardHeatQuotientDv N D v x) v :=
  (hasDerivAt_gaussianHeatFlow_variance hN hv x).div
    (hasDerivAt_gaussianHeatFlow_variance hD hv x) hpos

/-- Actual heat derivatives give the quotient backward generator, with
logarithmic denominator gradient. -/
theorem backwardHeatQuotient_heat_generator (N D : ℝ → ℝ) (v x : ℝ)
    (hpos : gaussianHeatFlow D v x ≠ 0) :
    -backwardHeatQuotientDv N D v x + (1 / 2 : ℝ) * backwardHeatQuotientDxx N D v x +
      (gaussianHeatFlow (deriv D) v x / gaussianHeatFlow D v x) *
        backwardHeatQuotientDx N D v x = 0 := by
  unfold backwardHeatQuotientDv backwardHeatQuotientDxx backwardHeatQuotientDx
  field_simp
  ring

end FRSB
