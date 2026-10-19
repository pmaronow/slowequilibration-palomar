-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedUniformCapHitDisorderAverage
public import SlowEquilibration.EntranceLatitudeOriginalMeanEvent

/-! The original latitude-good tensor bank's proved Gaussian failure
probability in the real-valued form used by the cap-hit integral bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped ENNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false

theorem originalLatitudeMeanGood_failure_real_le {n : ℕ} (hn : 1≤n)
    (μ : FiniteMixture) :
    (disorderLaw (n+1) μ.maxDegree).real
      (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ)ᶜ ≤
      Real.exp (-((n+1 : ℕ) : ℝ))+
        (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
          (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((n+1 : ℕ) : ℝ)))
  let b : ℝ≥0∞ :=
    (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ≥0∞)*
      ENNReal.ofReal (2*Real.exp (-((n+1 : ℕ) : ℝ)/2))
  have hFail := EntranceLatitudeTangentObservable.originalLatitudeMeanGood_failure_probability
    hn μ
  change disorderLaw (n+1) μ.maxDegree
    (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ)ᶜ≤a+b at hFail
  have hr := ENNReal.toReal_mono (by finiteness : a+b≠∞) hFail
  have hsum := ENNReal.toReal_add_le (a:=a) (b:=b)
  have hb : b.toReal =
      (EntranceLatitudeTangentObservable.originalLatitudeBankCount μ : ℝ)*
        (2*Real.exp (-((n+1 : ℕ) : ℝ)/2)) := by
    dsimp only [b]
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal
      (by positivity : 0≤2*Real.exp (-((n+1 : ℕ) : ℝ)/2))]
    simp
  have ha : a.toReal=Real.exp (-((n+1 : ℕ) : ℝ)) := by
    exact ENNReal.toReal_ofReal (Real.exp_nonneg _)
  calc
    (disorderLaw (n+1) μ.maxDegree).real
        (EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ)ᶜ ≤
      (a+b).toReal := hr
    _ ≤ a.toReal+b.toReal := hsum
    _ = _ := by rw [ha,hb]

end SlowEquilibration.ConditionedEntrance
