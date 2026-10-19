-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairedTensorProjectionGaussianEnvelope
public import SlowEquilibration.PairedTensorProjectionPosterior
public import SlowEquilibration.OrderedTensorSlotPermutation

/-! Literal original tensor-law and degree-block consumers of the true
all-order projected Gaussian envelope. -/

@[expose] public section
namespace SlowEquilibration.PairedTensorProjectionFeatures
noncomputable section
open MeasureTheory ProbabilityTheory
open SphericalAging.FiniteModel (TensorIndex normalization)
open PureTensorJetBounds SphericalModel OrderedTensorTraceGaussianBank
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def originalPairedEnvelope (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) : ℝ :=
  pairedGaussianEnvelope N q j (WithLp.toLp 2 J)

def originalProjectedTrace (N q j : ℕ) (J : SphericalAging.FiniteModel.Disorder N (q+j+j))
    (x : Vector N) : ℝ :=
  normalization N (q+j+j)/Real.sqrt N*inner ℝ (pairedTensorFeature N q j x) (WithLp.toLp 2 J)

/-- Exact physical observable in the genuine original tensor coordinates. -/
theorem originalProjectedTrace_physicalAxis_eq {N : ℕ} (hN : 2≤N) (q j : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (u : UnitSphere N) :
    originalProjectedTrace N q j J (physicalAxis u)=
      inner ℝ (pairedGaussianFeature N q j u) (WithLp.toLp 2 J) := by
  rw [originalProjectedTrace,pairedTensorFeature_physicalAxis_eq hN,
    real_inner_smul_left,pairedGaussianFeature,real_inner_smul_left,pairedPhysicalScale]
  ring

theorem originalProjectedTrace_abs_le_envelope {N : ℕ} (hN : 2≤N) (q j : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (u : UnitSphere N) :
    |originalProjectedTrace N q j J (physicalAxis u)| ≤ originalPairedEnvelope N q j J := by
  let : NeZero N := ⟨by omega⟩
  rw [originalProjectedTrace_physicalAxis_eq hN]
  exact norm_inner_le_absoluteSupremum _ (pairedGaussianFeature_continuous N q j) _ u

theorem originalPairedEnvelope_integrable {N : ℕ} (hN : 2≤N) (q j : ℕ) :
    Integrable (originalPairedEnvelope N q j) (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := by
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N (q+j+j) →
      EuclideanSpace ℝ (TensorIndex N (q+j+j)))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j)))
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := ⟨by fun_prop,rfl⟩
  exact hLaw.integrable_comp (pairedGaussianEnvelope_integrable hN q j)

/-- Actual iid original disorder expected uniform projected trace scale. -/
theorem expected_originalPairedEnvelope_le {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j) :
    (∫ J,originalPairedEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      2*Real.sqrt ((q : ℝ)+4*j)*(N : ℝ)^((1-(j : ℝ))/2) := by
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N (q+j+j) →
      EuclideanSpace ℝ (TensorIndex N (q+j+j)))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j)))
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := ⟨by fun_prop,rfl⟩
  rw [show (∫ J,originalPairedEnvelope N q j J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j))=
    ∫ g,pairedGaussianEnvelope N q j g ∂SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j)) from
      hLaw.integral_comp (pairedGaussianEnvelope_integrable hN q j).aestronglyMeasurable]
  exact expected_pairedGaussianEnvelope_le_dimension_scale hN q j hj

/-- Literal iid disorder upper-tail event, uniform over every physical axis. -/
theorem originalPairedEnvelope_upper_tail {N : ℕ} (hN : 2≤N) (q j : ℕ) (hj : 0<j)
    {s : ℝ} (hs : 0≤s) :
    SphericalAging.FiniteModel.disorderLaw N (q+j+j)
      {J | 2*Real.sqrt ((q : ℝ)+4*j)+s≤originalPairedEnvelope N q j J} ≤
      ENNReal.ofReal (2*Real.exp (-s^2*(N : ℝ)/2)) := by
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N (q+j+j) →
      EuclideanSpace ℝ (TensorIndex N (q+j+j)))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (q+j+j)))
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) := ⟨by fun_prop,rfl⟩
  have h := pairedGaussianEnvelope_upper_tail hN q j hj hs
  have hm : MeasurableSet {g : EuclideanSpace ℝ (TensorIndex N (q+j+j)) |
      2*Real.sqrt ((q : ℝ)+4*j)+s≤pairedGaussianEnvelope N q j g} :=
    (isClosed_le continuous_const (pairedGaussianEnvelope_lipschitz hN q j hj).continuous).measurableSet
  nth_rw 1 [←hLaw.map_eq] at h
  rw [Measure.map_apply_of_aemeasurable hLaw.aemeasurable hm] at h
  exact h

/-- The actual embedded mixed coefficient seed extracts precisely this original degree block. -/
theorem pairedDegreeSeed_inner_eq {N : ℕ} (P q j : ℕ) (hp : 2≤q+j+j) (hP : q+j+j≤P)
    (x : Vector N) (g : EuclideanDisorder N P) :
    inner ℝ (pairedDegreeSeed P q j hp hP x) g=
      inner ℝ (pairedTensorFeature N q j x)
        (WithLp.toLp 2 (unpackDisorder g (projectionDegree P q j hp hP))) := by
  classical
  simp only [pairedDegreeSeed,euclideanDisorder,flatDisorder,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single (projectionDegree P q j hp hP)]
  · simp only [projectedDegreeDisorder,Pi.single_eq_same,unpackDisorder]
    rfl
  · intro p hp' hne
    simp only [projectedDegreeDisorder,Pi.single_eq_of_ne hne,Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  · simp

/-- The pointwise posterior transfer yields the genuine normalized original
projected trace, at the posterior's own axis and every mixed mark. -/
theorem actual_mixedPosterior_originalProjectedTrace {n : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (q j : ℕ) (hj : 0<j) (hp : 2≤q+j+j) (hP : q+j+j≤μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (b : EuclideanSpace ℝ (Fin 2)) (g : EuclideanDisorder (n+1) μ.maxDegree) :
    originalProjectedTrace (n+1) q j
      (unpackDisorder (SphericalPosteriorMaps.mixedPosterior n μ Q u b g) (projectionDegree μ.maxDegree q j hp hP)) u=
    originalProjectedTrace (n+1) q j (unpackDisorder g (projectionDegree μ.maxDegree q j hp hP)) u := by
  unfold originalProjectedTrace
  rw [←pairedDegreeSeed_inner_eq,←pairedDegreeSeed_inner_eq,
    actual_mixedPosterior_pairedDegree_inner n μ Q q j hj hp hP u hu]

/-- Proper pure/value conditioning has the same actual physical trace transfer. -/
theorem actual_valuePosterior_originalProjectedTrace {n : ℕ} (μ : FiniteMixture)
    (Q : ℝ) (q j : ℕ) (hj : 0<j) (hp : 2≤q+j+j) (hP : q+j+j≤μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : ℝ) (g : EuclideanDisorder (n+1) μ.maxDegree) :
    originalProjectedTrace (n+1) q j
      (unpackDisorder (SphericalPosteriorMaps.valuePosterior n μ Q u e g) (projectionDegree μ.maxDegree q j hp hP)) u=
    originalProjectedTrace (n+1) q j (unpackDisorder g (projectionDegree μ.maxDegree q j hp hP)) u := by
  unfold originalProjectedTrace
  rw [←pairedDegreeSeed_inner_eq,←pairedDegreeSeed_inner_eq,
    actual_valuePosterior_pairedDegree_inner n μ Q q j hj hp hP u hu]

end
end SlowEquilibration.PairedTensorProjectionFeatures
