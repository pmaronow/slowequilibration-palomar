module
public import QuantitativeFollowup.QuadraticTilt

@[expose] public section

/-! Dominated differentiation of actual probability integrals under
bounded quadratic perturbations. All domination estimates are discharged
from explicit bounded observables. -/
noncomputable section
open MeasureTheory Set
open scoped Topology
namespace QuantitativeFollowup

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
  (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
  (Kf Kg : ℝ) (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg)
  (hfb : ∀ x, |f x| ≤ Kf) (hgb : ∀ x, |g x| ≤ Kg)

include hf hg Kf Kg hKf hKg hfb hgb

theorem integrable_quadraticTiltWeight (t : ℝ) : Integrable (quadraticTiltWeight f g t) P := by
  apply (integrable_const (Real.exp (|t| *Kf+|t| ^2*Kg/2))).mono'
  · exact (by unfold quadraticTiltWeight; fun_prop : Measurable (quadraticTiltWeight f g t)).aestronglyMeasurable
  · exact .of_forall (quadraticTiltWeight_bound f g Kf Kg |t| t hKf hKg (abs_nonneg t) hfb hgb le_rfl)

theorem integrable_quadraticTiltSlope (t : ℝ) : Integrable (quadraticTiltSlope f g t) P := by
  apply (integrable_const ((Kf+|t| *Kg)*Real.exp (|t| *Kf+|t| ^2*Kg/2))).mono'
  · exact (by unfold quadraticTiltSlope quadraticTiltWeight; fun_prop : Measurable (quadraticTiltSlope f g t)).aestronglyMeasurable
  · exact .of_forall (quadraticTiltSlope_bound f g Kf Kg |t| t hKf hKg (abs_nonneg t) hfb hgb le_rfl)

theorem integrable_quadraticTiltCurvature (t : ℝ) : Integrable (quadraticTiltCurvature f g t) P := by
  apply (integrable_const (((Kf+|t| *Kg)^2+Kg)*Real.exp (|t| *Kf+|t| ^2*Kg/2))).mono'
  · exact (by unfold quadraticTiltCurvature quadraticTiltWeight; fun_prop : Measurable (quadraticTiltCurvature f g t)).aestronglyMeasurable
  · exact .of_forall (quadraticTiltCurvature_bound f g Kf Kg |t| t hKf hKg (abs_nonneg t) hfb hgb le_rfl)

theorem hasDerivAt_integral_quadraticTiltWeight (t : ℝ) :
    HasDerivAt (fun t => ∫ x, quadraticTiltWeight f g t x ∂P)
      (∫ x, quadraticTiltSlope f g t x ∂P) t := by
  let R := |t|+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have htb (u : ℝ) (hu : u ∈ Icc (t-1) (t+1)) : |u| ≤ R := by
    rw [abs_le]
    dsimp [R]
    constructor <;> linarith [hu.1,hu.2,le_abs_self t,neg_le_abs t]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (F := quadraticTiltWeight f g) (F' := quadraticTiltSlope f g)
    (bound := fun _ => (Kf+R*Kg)*Real.exp (R*Kf+R^2*Kg/2))
    (.of_forall fun u => (by unfold quadraticTiltWeight; fun_prop :
      Measurable (quadraticTiltWeight f g u)).aestronglyMeasurable)
    (integrable_quadraticTiltWeight P f g hf hg Kf Kg hKf hKg hfb hgb t)
    (by exact (by unfold quadraticTiltSlope quadraticTiltWeight; fun_prop :
      Measurable (quadraticTiltSlope f g t)).aestronglyMeasurable)
    (.of_forall fun x u hu => quadraticTiltSlope_bound f g Kf Kg R u
      hKf hKg hR hfb hgb (htb u hu) x)
    (integrable_const _)
    (.of_forall fun x u _hu => hasDerivAt_quadraticTiltWeight f g x u)).2

theorem hasDerivAt_integral_quadraticTiltSlope (t : ℝ) :
    HasDerivAt (fun t => ∫ x, quadraticTiltSlope f g t x ∂P)
      (∫ x, quadraticTiltCurvature f g t x ∂P) t := by
  let R := |t|+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have htb (u : ℝ) (hu : u ∈ Icc (t-1) (t+1)) : |u| ≤ R := by
    rw [abs_le]
    dsimp [R]
    constructor <;> linarith [hu.1,hu.2,le_abs_self t,neg_le_abs t]
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Icc_mem_nhds (by linarith : t-1<t) (by linarith : t<t+1))
    (F := quadraticTiltSlope f g) (F' := quadraticTiltCurvature f g)
    (bound := fun _ => ((Kf+R*Kg)^2+Kg)*Real.exp (R*Kf+R^2*Kg/2))
    (.of_forall fun u => (by unfold quadraticTiltSlope quadraticTiltWeight; fun_prop :
      Measurable (quadraticTiltSlope f g u)).aestronglyMeasurable)
    (integrable_quadraticTiltSlope P f g hf hg Kf Kg hKf hKg hfb hgb t)
    (by exact (by unfold quadraticTiltCurvature quadraticTiltWeight; fun_prop :
      Measurable (quadraticTiltCurvature f g t)).aestronglyMeasurable)
    (.of_forall fun x u hu => quadraticTiltCurvature_bound f g Kf Kg R u
      hKf hKg hR hfb hgb (htb u hu) x)
    (integrable_const _)
    (.of_forall fun x u _hu => hasDerivAt_quadraticTiltSlope f g x u)).2

end QuantitativeFollowup
