-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailEnvelopes

/-! Integrating an absolute exponential density envelope, independent of
the possibly discontinuous value of the density at the tail threshold. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory
set_option maxHeartbeats 300000

theorem tail_upper_of_absolute_exponential_envelope {f : ℝ → ℝ}
    (hi : Integrable f) {A c h : ℝ} (hc : 0 < c)
    (henv : ∀ v : ℝ, 0 ≤ v → f (h+v) ≤ A*Real.exp (-c*v)) :
    tail f h ≤ A/c := by
  have hg : IntegrableOn (fun v : ℝ => Real.exp (-c*v)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0)
  rw [tail_eq_shift]
  have hh := integral_mono_ae ((hi.comp_add_left h).integrableOn (s := Ici 0))
    (hg.const_mul A) (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
      exact henv v hv)
  refine hh.trans_eq ?_
  rw [integral_const_mul,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (neg_neg_of_pos hc)]
  simp only [mul_zero,Real.exp_zero]
  ring

/-- Integrating a one-unit lower density envelope needs no continuity. -/
theorem tail_lower_of_absolute_unit_envelope {f : ℝ → ℝ}
    (hi : Integrable f) (hf : ∀ H : ℝ, 0 ≤ f H) {A h : ℝ}
    (henv : ∀ v ∈ Icc (0 : ℝ) 1, A ≤ f (h+v)) :
    A ≤ tail f h := by
  rw [tail_eq_shift]
  have hconst : IntegrableOn (fun _ : ℝ => A) (Icc 0 1) :=
    integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hsmall : A ≤ ∫ v in Icc (0 : ℝ) 1,f (h+v) := by
    have hh := integral_mono_ae hconst
      ((hi.comp_add_left h).integrableOn (s := Icc 0 1)) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
        exact henv v hv)
    rw [setIntegral_const,Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
    simpa only [sub_zero,one_smul] using hh
  exact hsmall.trans (setIntegral_mono_set
    ((hi.comp_add_left h).integrableOn (s := Ici 0))
    (ae_of_all _ (fun v => hf (h+v)))
    (ae_of_all _ (fun _ hv => hv.1)))

end SlowEquilibration.ExpectedTailCentering
