module
public import FRSB.MomentKernel
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! Closed-interval form of the deterministic moment-kernel detection lemma.
The clamp provides a global Lipschitz extension while preserving every physical
covariance-kernel value. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace FRSB

def momentUnitClamp (f : ℝ → ℝ) (s : ℝ) : ℝ :=
  f (projIcc (0 : ℝ) 1 (by norm_num) s)

@[simp] theorem momentUnitClamp_eq (f : ℝ → ℝ) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : momentUnitClamp f s = f s := by
  simp only [momentUnitClamp, projIcc_of_mem (by norm_num) hs, Subtype.coe_mk]

/-- An interior derivative bound and endpoint continuity give the actual
Lipschitz bound on the clamped moment function. -/
theorem lipschitzWith_momentUnitClamp (f g : ℝ → ℝ) (K : ℝ≥0)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g s) s)
    (hg : ∀ s ∈ Ioo (0 : ℝ) 1, ‖g s‖ ≤ K) :
    LipschitzWith K (momentUnitClamp f) := by
  have hi : LipschitzOnWith K f (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun s hs => by exact_mod_cast hg s hs)
  have hclosed : LipschitzOnWith K f (Icc (0 : ℝ) 1) := by
    have hc' : ContinuousOn f (closure (Ioo (0 : ℝ) 1)) := by
      simpa only [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using hc
    simpa only [closure_Ioo (show (0 : ℝ) ≠ 1 by norm_num)] using hi.closure hc'
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let px := projIcc (0 : ℝ) 1 (by norm_num) x
  let py := projIcc (0 : ℝ) 1 (by norm_num) y
  have hf := hclosed.dist_le_mul px px.property py py.property
  have hp := (LipschitzWith.projIcc (show (0 : ℝ) ≤ 1 by norm_num)).dist_le_mul x y
  simp only [NNReal.coe_one, one_mul] at hp
  change dist (f px) (f py) ≤ _
  exact hf.trans (mul_le_mul_of_nonneg_left hp K.coe_nonneg)

lemma hasDerivAt_momentUnitClamp (f : ℝ → ℝ) {s d : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) 1) (hd : HasDerivAt f d s) :
    HasDerivAt (momentUnitClamp f) d s := by
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  exact momentUnitClamp_eq f ⟨hr.1.le, hr.2.le⟩

/-- The moment-kernel conclusion needs derivative information only on the
physical interior, with ordinary continuity at both endpoints. -/
theorem tailIntegral_eq_zero_of_unitMomentKernel_zero (a f g : ℝ → ℝ)
    (ha : Measurable a) (hab : ∀ s, ‖a s‖ ≤ 1) (K : ℝ≥0)
    (hc : ContinuousOn f (Icc (0 : ℝ) 1))
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1, HasDerivAt f (g s) s)
    (hbound : ∀ s ∈ Ioo (0 : ℝ) 1, ‖g s‖ ≤ K)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, g s ≠ 0)
    (hz : ∀ t ∈ Ioo (0 : ℝ) 1, (∫ s in (0 : ℝ)..1, a s * f (min s t)) = 0) :
    ∀ t ∈ Ioo (0 : ℝ) 1, (∫ s in t..1, a s) = 0 := by
  apply tailIntegral_eq_zero_of_momentKernel_zero a (momentUnitClamp f) g ha hab K
    (lipschitzWith_momentUnitClamp f g K hc hd hbound)
    (fun s hs => hasDerivAt_momentUnitClamp f hs (hd s hs)) hpos
  intro t ht
  calc
    _ = ∫ s in (0 : ℝ)..1, a s * f (min s t) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at hs
      change a s * momentUnitClamp f (min s t) = a s * f (min s t)
      rw [momentUnitClamp_eq f
        ⟨le_min hs.1 ht.1.le, (min_le_left s t).trans hs.2⟩]
    _ = 0 := hz t ht

end FRSB
