-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
noncomputable section
namespace SlowEquilibration.ENNRadialIntegralBridge
open Set MeasureTheory
open scoped ENNReal

theorem iterated_toReal_eq (F : ℝ → ℝ → ℝ≥0∞) (U I : Set ℝ)
    (hjoint : Measurable (fun p : ℝ × ℝ => F p.1 p.2))
    (hfinite : ∀ H k : ℝ,F H k ≠ ⊤)
    (hi : ∀ H : ℝ,IntegrableOn (fun k => (F H k).toReal) U) :
    (∫⁻ H in I,∫⁻ k in U,F H k).toReal=
      ∫ H in I,∫ k in U,(F H k).toReal := by
  have hinner : Measurable (fun H : ℝ => ∫⁻ k in U,F H k) :=
    hjoint.lintegral_prod_right' (ν := volume.restrict U)
  have hF : ∀ H : ℝ,Measurable (F H) :=
    fun H => hjoint.comp (by fun_prop : Measurable (fun k : ℝ => (H,k)))
  have hinnerFinite : ∀ H : ℝ,(∫⁻ k in U,F H k) ≠ ⊤ := fun H =>
    (integrable_toReal_iff (hF H).aemeasurable (ae_of_all _ (hfinite H))).mp (hi H)
  rw [←integral_toReal hinner.aemeasurable (ae_of_all _ (fun H => lt_top_iff_ne_top.mpr (hinnerFinite H)))]
  apply integral_congr_ae
  apply ae_of_all
  intro H
  exact (integral_toReal (hF H).aemeasurable
    (ae_of_all _ (fun k => lt_top_iff_ne_top.mpr (hfinite H k)))).symm

end SlowEquilibration.ENNRadialIntegralBridge
