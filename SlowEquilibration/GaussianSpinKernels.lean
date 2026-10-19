-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinHessian
public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Integral
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-! Actual Gibbs kernels for bounded measurable features on an arbitrary
spin measure. Gaussian posterior transitions can be composed with these
kernels while retaining the original spin space and its null sets. -/

namespace SlowEquilibration.GaussianSpinInterpolation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal

variable {V H : Type*} [MeasurableSpace V] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

theorem measurable_feature_evaluation (L : V → H →L[ℝ] ℝ) (hL : Measurable L) :
    Measurable (fun p : H × V => L p.2 p.1) := by
  have he : Continuous (fun p : (H →L[ℝ] ℝ) × H => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  exact he.measurable.comp ((hL.comp measurable_snd).prodMk measurable_fst)

/-- The true Gibbs probability as a measurable kernel of the disorder. -/
def gibbsKernel (ν : Measure V) [IsFiniteMeasure ν] (L : V → H →L[ℝ] ℝ) : Kernel H V :=
  (Kernel.const H ν).withDensity (fun w v => ENNReal.ofReal
    (Real.exp (L v w) / moment ν (fun _ => 1) L w))

theorem gibbsKernel_apply (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    gibbsKernel ν L w = gibbsMeasure ν L w := by
  have hz : Measurable (moment ν (fun _ => 1) L) :=
    (moment_contDiff ν (fun _ => 1) L measurable_const hL (C := 1) (by norm_num) hK
      (hb.mono fun _ hv => ⟨by norm_num, hv⟩)).continuous.measurable
  have hd : Measurable (fun p : H × V => ENNReal.ofReal
      (Real.exp (L p.2 p.1) / moment ν (fun _ => 1) L p.1)) :=
    ((measurable_feature_evaluation L hL).exp.div (hz.comp measurable_fst)).ennreal_ofReal
  rw [gibbsKernel, Kernel.withDensity_apply _ hd]
  rfl

theorem gibbsKernel_markov (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) : IsMarkovKernel (gibbsKernel ν L) := by
  constructor
  intro w
  rw [gibbsKernel_apply ν L hL hK hb]
  exact gibbsMeasure_probability ν L hL hb w

theorem gibbsKernel_absolutelyContinuous (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) :
    gibbsKernel ν L w ≪ ν := by
  rw [gibbsKernel_apply ν L hL hK hb]
  exact gibbsMeasure_absolutelyContinuous ν L w

theorem integral_gibbsKernel (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (w : H) (ρ : V → ℝ) :
    (∫ v, ρ v ∂gibbsKernel ν L w) = expectation ν ρ L w := by
  rw [gibbsKernel_apply ν L hL hK hb]
  exact integral_gibbsMeasure ν L hL hb w ρ

/-- Conditional laws are ordinary composed Markov kernels, on the actual
spin space, rather than a replacement by a finite spin set. -/
def transportedSpinKernel (G : Kernel H V) (κ : ℕ → Kernel H H) : ℕ → Kernel H V
  | 0 => G
  | j+1 => transportedSpinKernel G κ j ∘ₖ κ j

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [BorelSpace H] in
theorem transportedSpinKernel_markov (G : Kernel H V) [IsMarkovKernel G]
    (κ : ℕ → Kernel H H) (hκ : ∀ j, IsMarkovKernel (κ j)) (j : ℕ) :
    IsMarkovKernel (transportedSpinKernel G κ j) := by
  induction j with
  | zero => exact inferInstanceAs (IsMarkovKernel G)
  | succ j ih =>
    have := hκ j
    have := ih
    exact inferInstanceAs (IsMarkovKernel (transportedSpinKernel G κ j ∘ₖ κ j))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H] [BorelSpace H] in
theorem transportedSpinKernel_absolutelyContinuous (G : Kernel H V)
    (κ : ℕ → Kernel H H) (ν : Measure V) (hG : ∀ w, G w ≪ ν)
    (j : ℕ) (w : H) : transportedSpinKernel G κ j w ≪ ν := by
  induction j generalizing w with
  | zero => exact hG w
  | succ j ih =>
    intro s hs
    have hν : ν (toMeasurable ν s) = 0 := by rw [measure_toMeasurable, hs]
    have hzero : ∀ y, transportedSpinKernel G κ j y (toMeasurable ν s) = 0 :=
      fun y => ih y hν
    apply measure_mono_null (subset_toMeasurable ν s)
    rw [transportedSpinKernel, Kernel.comp_apply' _ _ _ (measurableSet_toMeasurable ν s)]
    simp_rw [hzero]
    simp

end
end SlowEquilibration.GaussianSpinInterpolation
