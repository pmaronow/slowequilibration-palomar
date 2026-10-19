-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NegativeDefiniteMatrices
public import SlowEquilibration.SphericalCriticalDetMeasurable
public import SlowEquilibration.ConditionedIntrinsicHessian

/-! A joint Borel mark for genuine negative intrinsic Hessians at every
actual spherical critical point, including the omitted chart pole. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorMaps
open MeasureTheory Set Function Metric
open SphericalModel SphericalGaussianJet WholeFieldRegression
open SphericalMarkedWindows SphereHessian SphereChartVolume SphericalChartKacRice
open SphericalKacRiceGluing SphericalMorse SphericalForm IntrinsicHessianLaw ConditionedIntrinsicHessian
open NegativeDefiniteOperators GOEAsymptotics OAI.CriticalSK
open scoped ENNReal Topology RealInnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma intrinsicMatrix_continuous {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) : Continuous (intrinsicMatrix c x hx) := by
  have hm : Continuous (hessianMatrix c x (tangentFrame x hx)) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    convert (jetCLM c 2 x ![tangentFrame x hx i, tangentFrame x hx j]).continuous using 1
    funext J
    exact (jetCLM_apply _ _ _ _ J).symm
  have hr : Continuous (fun J : Disorder (n+1) P => jet c 1 x (fun _ => x) J / (n+1 : ℕ)) := by
    simpa only [jetCLM_apply] using (jetCLM c 1 x (fun _ => x)).continuous.div_const ((n+1 : ℕ):ℝ)
  have h := hm.sub (hr.smul (continuous_const (y := (1 : Matrix (Fin n) (Fin n) ℝ))))
  convert h using 1
  funext J
  exact (intrinsicHessian_toMatrix c J x hx).trans (by rw [radialMultiplier_eq_jet]; rfl)

lemma matrixOperator_measurable (n : ℕ) :
    Measurable (fun W : Matrix (Fin n) (Fin n) ℝ => gaussianMatrixCLM (matrixToGaussian W)) :=
  (gaussianMatrixCLM_continuous n).measurable.comp (matrixToGaussian_measurable n)

def criticalNegative {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) : Prop :=
  if x = southPole n then NegativeDefinite (gaussianMatrixCLM (matrixToGaussian
    (intrinsicMatrix c (southPole n) (southPole_norm_sq n) J)))
  else NegativeDefinite (coordinateHessian n c J (manuscriptChartInverse n x))

lemma criticalNegative_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    MeasurableSet {p : Disorder (n+1) P × Vector (n+1) | criticalNegative n c p.1 p.2} := by
  have hp := (isOpen_negativeDefinite (E := EuclideanSpace ℝ (Fin n))).measurableSet.preimage
    ((matrixOperator_measurable n).comp (intrinsicMatrix_continuous c (southPole n) (southPole_norm_sq n)).measurable)
  have hi : Measurable (fun p : Disorder (n+1) P × Vector (n+1) => manuscriptChartInverse n p.2) :=
    (manuscriptChartInverse_measurable n).comp measurable_snd
  have hc := (isOpen_negativeDefinite (E := EuclideanSpace ℝ (Fin n))).measurableSet.preimage
    ((coordinateHessian_measurable n c).comp (measurable_fst.prodMk hi))
  have heq : MeasurableSet {p : Disorder (n+1) P × Vector (n+1) | p.2 = southPole n} :=
    measurableSet_eq_fun measurable_snd measurable_const
  convert MeasurableSet.ite heq (hp.preimage measurable_fst) hc using 1
  ext p
  by_cases hx : p.2 = southPole n <;> simp [criticalNegative, Set.ite, hx]

lemma criticalNegative_iff {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (hcrit : surfaceGradient (field c J) x = 0) :
    criticalNegative n c J x ↔ NegativeDefinite (intrinsicHessian (field c J) x) := by
  by_cases hp : x = southPole n
  · subst x
    simp only [criticalNegative, ite_true]
    exact negativeDefinite_toMatrix_iff (tangentBasis (southPole n) (southPole_norm_sq n)) _
  · have him : x ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨hx,hp⟩
    obtain ⟨u,hu,rfl⟩ := him
    have hu' : ‖u‖ < 2 := by simpa using hu
    rw [criticalNegative, ite_eq_right hp, manuscriptChartInverse_left_inv hu',
      coordinateHessian_eq n c J hu', actualChartHessian_eq_pullback c J hu' hcrit,
      negativeDefinite_pullback_iff]

def negativeHessianMark {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (J : Disorder (n+1) P) (x : Vector (n+1)) : ℝ≥0∞ :=
  if criticalNegative n c J x then 1 else 0

lemma negativeHessianMark_measurable {P : ℕ} (n : ℕ) (c : Degree P → ℝ) :
    Measurable (fun p : Disorder (n+1) P × Vector (n+1) => negativeHessianMark n c p.1 p.2) :=
  Measurable.ite (criticalNegative_measurable n c) measurable_const measurable_const

lemma negativeHessianMark_eq {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (J : Disorder (n+1) P)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (hcrit : surfaceGradient (field c J) x = 0) :
    negativeHessianMark n c J x = if NegativeDefinite (intrinsicHessian (field c J) x) then 1 else 0 := by
  simp only [negativeHessianMark, criticalNegative_iff n c J x hx hcrit]

end
end SlowEquilibration.SphericalPosteriorMaps
