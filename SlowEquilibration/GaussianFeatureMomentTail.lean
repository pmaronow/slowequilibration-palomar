-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDistanceLowerTail
public import SlowEquilibration.SphericalMomentLower

@[expose] public section

/-! The actual Paley--Zygmund / truncated-feature lower-tail argument. The
constants depend on genuine first and second moment bounds; all Gaussian
set enlargement and feature-good-set probabilities are proved internally. -/

noncomputable section
namespace SlowEquilibration.GaussianFeatureMomentTail
open MeasureTheory ProbabilityTheory Set Metric
open scoped Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι]
abbrev E := EuclideanSpace ℝ ι
abbrev law := SYK.standardGaussianMeasureOnEuclidean ι

def featureRadius (B D : ℝ) : ℝ := Real.sqrt (32*B*(D+1))
def tailSlope (B D : ℝ) : ℝ := 4*featureRadius B D
def tailOffset (B D : ℝ) : ℝ := Real.log 4+
  tailSlope B D*Real.sqrt (-2*Real.log (1/(32*B)))

theorem tailSlope_pos {B D : ℝ} (hB : 0<B) (hD : 0 ≤ D) : 0<tailSlope B D := by
  unfold tailSlope featureRadius
  positivity

theorem tailOffset_pos {B D : ℝ} (hB : 0<B) (hD : 0 ≤ D) : 0<tailOffset B D := by
  have hlog : 0<Real.log (4:ℝ) := Real.log_pos (by norm_num)
  unfold tailOffset
  exact add_pos_of_pos_of_nonneg hlog
    (mul_nonneg (tailSlope_pos hB hD).le (Real.sqrt_nonneg _))

/-- Genuine finite-dimensional Gaussian lower-tail bound, from a true
truncated mass and its true normalized feature integral. -/
theorem lower_tail_le (Y : E (ι:=ι) → ℝ) (V : E (ι:=ι) → E (ι:=ι))
    (hYm : Measurable Y) (hYi : Integrable Y (law (ι:=ι)))
    (hY2i : Integrable (fun x => Y x^2) (law (ι:=ι))) (hY0 : ∀ᵐx ∂law (ι:=ι),0 ≤ Y x)
    (hVm : Measurable V) (hV2i : Integrable (fun x => ‖V x‖^2) (law (ι:=ι)))
    {B D A : ℝ} (hB : 0<B) (hD : 0 ≤ D)
    (hMean : (1/2:ℝ) ≤ ∫x,Y x ∂law (ι:=ι))
    (hSecond : (∫x,Y x^2 ∂law (ι:=ι)) ≤ B)
    (hFeature : (∫x,‖V x‖^2 ∂law (ι:=ι)) ≤ D)
    (f : E (ι:=ι) → ℝ)
    (hSupport : ∀x y,0<Y y →
      A+Real.log (Y y)-(‖V y‖/Y y)*dist x y ≤ f x)
    {s : ℝ} (hs : 0 ≤ s) :
    (law (ι:=ι)).real {x | f x ≤ A-tailOffset B D-tailSlope B D*s} ≤ Real.exp (-s^2/2) := by
  let W := 32*B*(D+1)
  let c := 1/(32*B)
  let P : Set (E (ι:=ι)) := {x | (1/4:ℝ) ≤ Y x}
  let Q : Set (E (ι:=ι)) := {x | W<‖V x‖^2}
  let G := P∩Qᶜ
  have hW : 0<W := by dsimp [W]; positivity
  have hc : 0<c := by dsimp [c]; positivity
  have hP : MeasurableSet P := measurableSet_le measurable_const hYm
  have hQ : MeasurableSet Q := measurableSet_lt measurable_const (hVm.norm.pow_const 2)
  have hG : MeasurableSet G := hP.inter hQ.compl
  have hpaley := SphericalMomentLower.paleyZygmund_half (law (ι:=ι)) Y hYm hYi hY2i hY0
    (show (0:ℝ)<1/2 by norm_num) hB hMean hSecond
  have hp : 2*c ≤ (law (ι:=ι)).real P := by
    have he : (1/2:ℝ)^2/(4*B)=2*c := by dsimp [c]; field_simp; ring
    simpa only [he,show (1/2:ℝ)/2=1/4 by norm_num,P] using hpaley
  have hm := mul_meas_ge_le_integral_of_nonneg
    (.of_forall fun x : E (ι:=ι) => sq_nonneg ‖V x‖) hV2i W
  have hQsub : Q⊆{x : E (ι:=ι) | W ≤ ‖V x‖^2} := by
    intro x hx
    change W<‖V x‖^2 at hx
    exact hx.le
  have hq : (law (ι:=ι)).real Q ≤ c := by
    have hh := (mul_le_mul_of_nonneg_left (measureReal_mono hQsub) hW.le).trans
      (hm.trans hFeature)
    have hDc : D ≤ W*c := by dsimp [W,c]; field_simp; linarith
    nlinarith [hh.trans hDc]
  have hg : c ≤ (law (ι:=ι)).real G := by
    have hsub : P⊆G∪Q := by intro x hx; by_cases hq : x∈Q <;> simp [G,hx,hq]
    have hh := (measureReal_mono (μ:=law (ι:=ι)) hsub).trans (measureReal_union_le (μ:=law (ι:=ι)) G Q)
    linarith
  have hEnvelope (x y : E (ι:=ι)) (hy : y∈G) :
      (A+Real.log (1/4:ℝ))-tailSlope B D*dist x y ≤ f x := by
    have hyY : (1/4:ℝ) ≤ Y y := hy.1
    have hyV : ‖V y‖^2 ≤ W := le_of_not_gt hy.2
    have hyY0 : 0<Y y := lt_of_lt_of_le (by norm_num) hyY
    have hnorm : ‖V y‖ ≤ featureRadius B D := by
      have hsqrt := Real.sq_sqrt hW.le
      change ‖V y‖ ≤ Real.sqrt W
      nlinarith [Real.sqrt_nonneg W,norm_nonneg (V y)]
    have hratio : ‖V y‖/Y y ≤ tailSlope B D := by
      apply (div_le_iff₀ hyY0).mpr
      have hR := mul_le_mul_of_nonneg_left hyY (tailSlope_pos hB hD).le
      dsimp [tailSlope] at hR ⊢
      nlinarith
    have hlog := Real.log_le_log (show (0:ℝ)<1/4 by norm_num) hyY
    have hh := hSupport x y hyY0
    have hprod := mul_le_mul_of_nonneg_right hratio (dist_nonneg : 0 ≤ dist x y)
    linarith
  have ht := GaussianDistanceLowerTail.affine_envelope_lower_tail hG hc
    (tailSlope_pos hB hD) hg hs f hEnvelope
  convert ht using 1
  congr 2
  ext x
  have hlog : Real.log (1/4:ℝ)=-Real.log 4 := by rw [one_div,Real.log_inv]
  simp only [tailOffset,c,hlog]
  ring_nf

end SlowEquilibration.GaussianFeatureMomentTail
