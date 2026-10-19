-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianBankAveraging
public import SlowEquilibration.SphericalPerturbationRadialPositivity

/-! True independent Gaussian-bank averaging of the finite tensor
positivity theorem. Joint Gibbs measurability, conditional normalization,
actual Gaussian bank independence and Fubini are all proved internally. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianSpinInterpolation

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory Topology

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V X H : Type*} [MeasurableSpace V] [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]

/-- The literal independently sampled Gibbs-pair mass at a jointly
parameterized realized coefficient vector. -/
def realizedPairMass (μ : Measure V) (T : V → H →L[ℝ] ℝ) (Φ : X → H)
    (A : Set (V × V)) (p : X) : ℝ :=
  ((gibbsMeasure μ T (Φ p)).prod (gibbsMeasure μ T (Φ p))).real A

theorem realizedPairMass_measurable (μ : Measure V) [IsProbabilityMeasure μ]
    (T : V → H →L[ℝ] ℝ) (hT : Measurable T) {B : ℝ} (hB : 0≤B)
    (hb : ∀ᵐ z ∂μ,‖T z‖≤B) (Φ : X → H) (hΦ : Measurable Φ)
    (A : Set (V × V)) (hA : MeasurableSet A) : Measurable (realizedPairMass μ T Φ A) := by
  let _ := gibbsKernel_markov μ T hT hB hb
  let G : Kernel X V := (gibbsKernel μ T).comap Φ hΦ
  have hm : Measurable (fun p => ((G ×ₖ G) p).real A) := by
    simpa only [Measure.real] using ((G ×ₖ G).measurable_coe hA).ennreal_toReal
  have heq : (fun p => ((G ×ₖ G) p).real A)=realizedPairMass μ T Φ A := by
    funext p
    rw [Kernel.prod_apply]
    change ((gibbsKernel μ T (Φ p)).prod (gibbsKernel μ T (Φ p))).real A=_
    rw [gibbsKernel_apply μ T hT hB hb]
    rfl
  rwa [heq] at hm

omit [MeasurableSpace X] [MeasurableSpace H] [BorelSpace H] in
theorem realizedPairMass_norm_le_one (μ : Measure V) [IsProbabilityMeasure μ]
    (T : V → H →L[ℝ] ℝ) (hT : Measurable T) {B : ℝ}
    (hb : ∀ᵐ z ∂μ,‖T z‖≤B) (Φ : X → H) (A : Set (V × V)) (p : X) :
    ‖realizedPairMass μ T Φ A p‖≤1 := by
  let _ := gibbsMeasure_probability μ T hT hb (Φ p)
  unfold realizedPairMass
  rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

end SlowEquilibration.GaussianSpinInterpolation

namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianCompactFeatureComparison
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology RealInnerProductSpace

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Uniform genuine negative-overlap control for a joined Gaussian bank
whose field is the sum of any bounded spherical Gaussian base bank and
the actual radial tensor perturbation. The ordinary exponent split may
include a fixed interpolation rotation and a true joint coefficient map.
No conditional-law identification or positivity premise is supplied. -/
theorem exists_uniform_independent_bank_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ, ∃ V : ℝ, 0<K ∧ 1≤V ∧
      ∀ {N : ℕ} (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
      {r : ℝ}, 0<r → (∀ᵐ z ∂μ,‖z‖=r) →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ), Measurable L →
      ∀ {B : ℝ}, (∀ᵐ z ∂μ,‖L z‖≤B) →
      ∀ (v : ℝ), V≤v →
      ∀ (T : Vector N → EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →L[ℝ] ℝ), Measurable T →
      ∀ {BT : ℝ}, 0≤BT → (∀ᵐ z ∂μ,‖T z‖≤BT) →
      ∀ (Φ : (Fin K → ℝ) × EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →
        EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)), Measurable Φ →
      (∀ (x : Fin K → ℝ) (D : EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)),
        ∀ᵐ z ∂μ,T z (Φ (x,D))=L z (sumSplit D).1+
          radialPerturbation (coefficients v x) r z (sumSplit D).2) →
      (∫x,∫D,realizedPairMass μ T Φ
        {z : Vector N × Vector N | radiusOverlap r z.1 z.2≤-ε} (x,D)
        ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ TensorCoordinate N K) ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_conditioned_radial_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N μ _ r hr hμ ι _ _ L hL B hb v hv T hT BT hBT hbT Φ hΦ hsplit
  let A : Set (Vector N × Vector N) := {z | radiusOverlap r z.1 z.2≤-ε}
  have hA : MeasurableSet A := by
    exact measurableSet_le (radiusOverlap_measurable N r) measurable_const
  let F := realizedPairMass μ T Φ A
  have hF : Measurable F := realizedPairMass_measurable μ T hT hBT hbT Φ hΦ A hA
  have hFb : ∀p,‖F p‖≤1 := realizedPairMass_norm_le_one μ T hT hbT Φ A
  have hNode (w : EuclideanSpace ℝ ι) :
      (∫x,∫z,F (x,sumJoin (w,z))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K)≤η := by
    have hp := hPos μ hr hμ (EuclideanSpace ℝ ι) L hL hb w v hv
    have heq : (∫x,∫z,F (x,sumJoin (w,z))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K)=
        ∫x,∫z,((gibbsMeasure (gibbsMeasure μ L w) (radialPerturbation (coefficients v x) r) z).prod
          (gibbsMeasure (gibbsMeasure μ L w) (radialPerturbation (coefficients v x) r) z)).real A
          ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K := by
      apply integral_congr_ae
      exact .of_forall fun x => by
        apply integral_congr_ae
        exact .of_forall fun z => by
          have hs : ∀ᵐ y ∂μ,T y (Φ (x,sumJoin (w,z)))=
              L y w+radialPerturbation (coefficients v x) r y z := by
            simpa only [sumSplit_sumJoin] using hsplit x (sumJoin (w,z))
          have hg := gibbsMeasure_associate μ L hL hb w (radialPerturbation (coefficients v x) r)
            (radialPerturbation_measurable _ r) z T hT hbT (Φ (x,sumJoin (w,z))) hs
          change ((gibbsMeasure μ T (Φ (x,sumJoin (w,z)))).prod
            (gibbsMeasure μ T (Φ (x,sumJoin (w,z))))).real A=_
          rw [← hg]
    exact heq.trans_le hp
  have hSwap := external_parameter_joined_gaussian_swap (positiveCubeLaw K) F hF hFb
  change (∫x,∫D,F (x,D) ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ TensorCoordinate N K)
    ∂positiveCubeLaw K)≤η
  rw [hSwap]
  have hNon : ∀ᵐ w ∂SYK.standardGaussianMeasureOnEuclidean ι,
      0≤(∫x,∫z,F (x,sumJoin (w,z))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) :=
    .of_forall fun w => integral_nonneg fun x => integral_nonneg fun z => measureReal_nonneg
  have hh := integral_mono_of_nonneg hNon (integrable_const η) (.of_forall hNode)
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end SlowEquilibration.SphericalPositivePerturbation
