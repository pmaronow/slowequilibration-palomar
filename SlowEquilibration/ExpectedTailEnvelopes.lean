-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailCentering
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Group.Integral

/-! True density envelopes give upper-tail comparison and decay. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory
set_option maxHeartbeats 300000

theorem tail_eq_shift (f : ℝ → ℝ) (h : ℝ) :
    tail f h=∫ v in Ici (0 : ℝ),f (h+v) := by
  calc
    tail f h=∫ x : ℝ,(Ici h).indicator f x := (integral_indicator measurableSet_Ici).symm
    _=∫ x : ℝ,(Ici h).indicator f (h+x) := (integral_add_left_eq_self _ h).symm
    _=∫ x : ℝ,(Ici (0 : ℝ)).indicator (fun x => f (h+x)) x := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      have he : h ≤ h+x ↔ 0 ≤ x := by constructor <;> intro hx <;> linarith
      simp only [Set.indicator,mem_Ici,he]
    _=∫ v in Ici (0 : ℝ),f (h+v) := integral_indicator measurableSet_Ici

theorem tail_upper_of_density_envelope {f : ℝ → ℝ} (hi : Integrable f) {c h : ℝ}
    (hc : 0 < c) (henv : ∀ v : ℝ,0 ≤ v → f (h+v) ≤ f h*Real.exp (-c*v)) :
    tail f h ≤ f h/c := by
  have hg : IntegrableOn (fun v : ℝ => Real.exp (-c*v)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_neg_of_pos hc) 0)
  rw [tail_eq_shift]
  have hh := integral_mono_ae ((hi.comp_add_left h).integrableOn (s := Ici 0)) (hg.const_mul (f h))
    (by filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv;exact henv v hv)
  refine hh.trans_eq ?_
  rw [integral_const_mul,integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hc)]
  simp only [mul_zero,Real.exp_zero]
  ring

theorem tail_lower_of_unit_density_envelope {f : ℝ → ℝ} (hi : Integrable f)
    (h0 : ∀ H : ℝ,0 ≤ f H) {c h : ℝ} (_hc : 0 ≤ c)
    (henv : ∀ v∈Icc (0 : ℝ) 1,Real.exp (-c)*f h ≤ f (h+v)) :
    Real.exp (-c)*f h ≤ tail f h := by
  rw [tail_eq_shift]
  have hsmall : Real.exp (-c)*f h ≤ ∫ v in Icc (0 : ℝ) 1,f (h+v) := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp (-c)*f h) (Icc 0 1) :=
      integrableOn_const (by rw [Real.volume_Icc];exact ENNReal.ofReal_ne_top)
    have hh := integral_mono_ae hconst ((hi.comp_add_left h).integrableOn (s := Icc 0 1))
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv;exact henv v hv)
    rw [setIntegral_const,Real.volume_real_Icc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hh
    simpa only [sub_zero,one_smul] using hh
  apply hsmall.trans
  exact setIntegral_mono_set ((hi.comp_add_left h).integrableOn (s := Ici 0))
    (ae_of_all _ (fun v => h0 (h+v))) (ae_of_all _ (fun _ hx => hx.1))

theorem tail_decay_of_density_envelope {f : ℝ → ℝ} (hi : Integrable f) {c h v : ℝ}
    (_hv : 0 ≤ v)
    (henv : ∀ H : ℝ,h ≤ H → f (H+v) ≤ f H*Real.exp (-c*v)) :
    tail f (h+v) ≤ tail f h*Real.exp (-c*v) := by
  rw [tail_eq_shift,tail_eq_shift]
  have hh := integral_mono_ae ((hi.comp_add_left (h+v)).integrableOn (s := Ici 0))
    (((hi.comp_add_left h).integrableOn (s := Ici 0)).mul_const (Real.exp (-c*v)))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with w hw
      have hw0 : 0 ≤ w := hw
      have he := henv (h+w) (by linarith)
      simpa only [add_assoc,add_left_comm,add_comm] using he)
  exact hh.trans_eq (integral_mul_const _ _)

end SlowEquilibration.ExpectedTailCentering
