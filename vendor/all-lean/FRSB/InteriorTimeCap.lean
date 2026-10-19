module
public import Paper.HJBVerification

@[expose] public section

/-! A globally C1 time map into an open cell, exact on a chosen cropped cell. -/
noncomputable section
open Set StochasticCalculus Paper
open scoped ContDiff
namespace FRSB

def interiorTimeCap (a l r b t : ℝ) : ℝ :=
  -hjbTimeCap (-l) ((l-a)/2) (-hjbTimeCap r ((b-r)/2) t)

def interiorTimeCapD (a l r b t : ℝ) : ℝ :=
  hjbTimeCapD (-l) ((l-a)/2) (-hjbTimeCap r ((b-r)/2) t) *
    hjbTimeCapD r ((b-r)/2) t

theorem hjbTimeCap_ge_min (c δ t : ℝ) (hδ : 0 < δ) : min c t ≤ hjbTimeCap c δ t := by
  unfold hjbTimeCap
  split_ifs with ht
  · exact min_le_right _ _
  · have htc : c < t := lt_of_not_ge ht
    have he : Real.exp (-(t-c)/δ) ≤ 1 := Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sub_nonneg.mpr htc.le)) hδ.le)
    rw [min_eq_left htc.le]
    have hh : 0 ≤ δ * (1-Real.exp (-(t-c)/δ)) := mul_nonneg hδ.le (sub_nonneg.mpr he)
    linarith

theorem interiorTimeCap_mem (a l r b : ℝ) (hal : a < l) (hlr : l ≤ r)
    (hrb : r < b) (t : ℝ) : interiorTimeCap a l r b t ∈ Ioo a b := by
  have hdl : 0 < (l-a)/2 := by linarith
  have hdr : 0 < (b-r)/2 := by linarith
  have hupper := hjbTimeCap_lt r hdr t
  have hlower := hjbTimeCap_lt (-l) hdl (-hjbTimeCap r ((b-r)/2) t)
  have hmin := hjbTimeCap_ge_min (-l) ((l-a)/2) (-hjbTimeCap r ((b-r)/2) t) hdl
  unfold interiorTimeCap
  constructor
  · linarith
  · have hh : -b < min (-l) (-hjbTimeCap r ((b-r)/2) t) := by
      exact lt_min (by linarith) (by linarith)
    linarith

theorem interiorTimeCap_eq (a l r b t : ℝ) (ht : t ∈ Icc l r) :
    interiorTimeCap a l r b t = t := by
  unfold interiorTimeCap
  rw [hjbTimeCap_of_le r ((b-r)/2) t ht.2,
    hjbTimeCap_of_le (-l) ((l-a)/2) (-t) (neg_le_neg ht.1), neg_neg]

theorem interiorTimeCapD_eq (a l r b t : ℝ) (ht : t ∈ Icc l r) :
    interiorTimeCapD a l r b t = 1 := by
  simp only [interiorTimeCapD, hjbTimeCap_of_le r ((b-r)/2) t ht.2,
    hjbTimeCapD, if_pos ht.2, if_pos (neg_le_neg ht.1), one_mul]

@[fun_prop] theorem continuous_interiorTimeCap (a l r b : ℝ) :
    Continuous (interiorTimeCap a l r b) := by
  unfold interiorTimeCap
  exact ((continuous_hjbTimeCap _ _).comp (continuous_hjbTimeCap r _).neg).neg

@[fun_prop] theorem continuous_interiorTimeCapD (a l r b : ℝ) :
    Continuous (interiorTimeCapD a l r b) := by
  unfold interiorTimeCapD
  exact ((continuous_hjbTimeCapD _ _).comp (continuous_hjbTimeCap r _).neg).mul
    (continuous_hjbTimeCapD r _)

theorem hasDerivAt_interiorTimeCap (a l r b : ℝ) (hal : a < l) (hrb : r < b) (t : ℝ) :
    HasDerivAt (interiorTimeCap a l r b) (interiorTimeCapD a l r b t) t := by
  have hd := ((hasDerivAt_hjbTimeCap (-l) (by linarith : 0 < (l-a)/2)
    (-hjbTimeCap r ((b-r)/2) t)).comp t
      (hasDerivAt_hjbTimeCap r (by linarith : 0 < (b-r)/2) t).neg).neg
  convert! hd using 1
  unfold interiorTimeCapD
  ring

def interiorCappedTest (f : ℝ → ℝ → ℝ) (a l r b t x : ℝ) : ℝ :=
  f (interiorTimeCap a l r b t) x

theorem interiorCappedTest_timeDerivative (f ft : ℝ → ℝ → ℝ)
    (a l r b : ℝ) (hal : a < l) (hlr : l ≤ r) (hrb : r < b)
    (ht : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => f s x) (ft t x) t) (t x : ℝ) :
    itoTimeDerivative (interiorCappedTest f a l r b) t x =
      ft (interiorTimeCap a l r b t) x * interiorTimeCapD a l r b t :=
  ((ht _ (interiorTimeCap_mem a l r b hal hlr hrb t) x).comp t
    (hasDerivAt_interiorTimeCap a l r b hal hrb t)).deriv

theorem interiorCappedTest_differentiable_time (f ft : ℝ → ℝ → ℝ)
    (a l r b : ℝ) (hal : a < l) (hlr : l ≤ r) (hrb : r < b)
    (ht : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => f s x) (ft t x) t) :
    ∀ x, Differentiable ℝ (fun t => interiorCappedTest f a l r b t x) := by
  intro x t
  exact ((ht _ (interiorTimeCap_mem a l r b hal hlr hrb t) x).comp t
    (hasDerivAt_interiorTimeCap a l r b hal hrb t)).differentiableAt

theorem interiorCappedTest_spaceDerivative (f fx : ℝ → ℝ → ℝ)
    (hx : ∀ t x, HasDerivAt (f t) (fx t x) x) (a l r b t x : ℝ) :
    itoSpaceDerivative (interiorCappedTest f a l r b) t x =
      fx (interiorTimeCap a l r b t) x := (hx _ x).deriv

theorem interiorCappedTest_spaceSecondDerivative (f fx fxx : ℝ → ℝ → ℝ)
    (hx : ∀ t x, HasDerivAt (f t) (fx t x) x)
    (hxx : ∀ t x, HasDerivAt (fx t) (fxx t x) x) (a l r b t x : ℝ) :
    itoSpaceSecondDerivative (interiorCappedTest f a l r b) t x =
      fxx (interiorTimeCap a l r b t) x := by
  unfold itoSpaceSecondDerivative
  have he : deriv (interiorCappedTest f a l r b t) = fx (interiorTimeCap a l r b t) :=
    funext (fun y => interiorCappedTest_spaceDerivative f fx hx a l r b t y)
  rw [he]
  exact (hxx _ x).deriv

theorem interiorCappedTest_regular (f ft fx fxx : ℝ → ℝ → ℝ)
    (a l r b : ℝ) (hal : a < l) (hlr : l ≤ r) (hrb : r < b)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hft : Continuous (fun p : ℝ × ℝ => ft p.1 p.2))
    (hfx : Continuous (fun p : ℝ × ℝ => fx p.1 p.2))
    (hfxx : Continuous (fun p : ℝ × ℝ => fxx p.1 p.2))
    (ht : ∀ t ∈ Ioo a b, ∀ x, HasDerivAt (fun s => f s x) (ft t x) t)
    (hx : ∀ t x, HasDerivAt (f t) (fx t x) x)
    (hxx : ∀ t x, HasDerivAt (fx t) (fxx t x) x)
    (hC2 : ∀ t, ContDiff ℝ 2 (f t)) :
    Continuous (fun p : ℝ × ℝ => interiorCappedTest f a l r b p.1 p.2) ∧
    (∀ x, Differentiable ℝ (fun t => interiorCappedTest f a l r b t x)) ∧
    (∀ t, ContDiff ℝ 2 (interiorCappedTest f a l r b t)) ∧
    Continuous (fun p : ℝ × ℝ => itoTimeDerivative (interiorCappedTest f a l r b) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => itoSpaceDerivative (interiorCappedTest f a l r b) p.1 p.2) ∧
    Continuous (fun p : ℝ × ℝ => itoSpaceSecondDerivative (interiorCappedTest f a l r b) p.1 p.2) := by
  have hm : Continuous (fun p : ℝ × ℝ => (interiorTimeCap a l r b p.1,p.2)) := by fun_prop
  refine ⟨hf.comp hm, interiorCappedTest_differentiable_time f ft a l r b hal hlr hrb ht,
    fun t => hC2 _, ?_, ?_, ?_⟩
  · simp_rw [interiorCappedTest_timeDerivative f ft a l r b hal hlr hrb ht]
    exact (hft.comp hm).mul ((continuous_interiorTimeCapD a l r b).comp continuous_fst)
  · simp_rw [interiorCappedTest_spaceDerivative f fx hx]
    exact hfx.comp hm
  · simp_rw [interiorCappedTest_spaceSecondDerivative f fx fxx hx hxx]
    exact hfxx.comp hm

end FRSB
