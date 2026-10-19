-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianIndependentBankPositivity

/-! Uniform actual negative-overlap bound on the manuscript sphere law
for independent bounded Gaussian base and radial tensor perturbation
banks. Sphere support and physical overlap normalization are internal. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianCompactFeatureComparison
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped ProbabilityTheory Topology RealInnerProductSpace

set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem radiusOverlap_sqrt_eq_overlap {N : ℕ} (x y : Vector N) :
    radiusOverlap (Real.sqrt N) x y=SphericalModel.overlap x y := by
  rw [radiusOverlap,SphericalModel.overlap,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- Genuine uniform perturbative negativity control under the original
uniform spherical law. Only the actual field-bank split and ordinary
measurability/operator bounds remain as model-specific inputs. -/
theorem exists_uniform_sphere_bank_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ, ∃ V : ℝ, 0<K ∧ 1≤V ∧
      ∀ {N : ℕ}, 1≤N →
      ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (L : Vector N → EuclideanSpace ℝ ι →L[ℝ] ℝ), Measurable L →
      ∀ {B : ℝ}, (∀ᵐ z ∂sphereLaw N,‖L z‖≤B) →
      ∀ (v : ℝ), V≤v →
      ∀ (T : Vector N → EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →L[ℝ] ℝ), Measurable T →
      ∀ {BT : ℝ}, 0≤BT → (∀ᵐ z ∂sphereLaw N,‖T z‖≤BT) →
      ∀ (Φ : (Fin K → ℝ) × EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →
        EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)), Measurable Φ →
      (∀ (x : Fin K → ℝ) (D : EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)),
        ∀ᵐ z ∂sphereLaw N,T z (Φ (x,D))=L z (sumSplit D).1+
          radialPerturbation (coefficients v x) (Real.sqrt N) z (sumSplit D).2) →
      (∫x,∫D,realizedPairMass (sphereLaw N) T Φ
        {z : Vector N × Vector N | SphericalModel.overlap z.1 z.2≤-ε} (x,D)
        ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ TensorCoordinate N K) ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_independent_bank_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N hN ι _ _ L hL B hb v hv T hT BT hBT hbT Φ hΦ hsplit
  have hNpos : 0<(N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hr : 0<Real.sqrt N := Real.sqrt_pos.mpr hNpos
  have ht := hPos (sphereLaw N) hr (sphereLaw_norm_ae hN) ι L hL hb v hv T hT hBT hbT Φ hΦ hsplit
  simpa only [radiusOverlap_sqrt_eq_overlap] using ht

end SlowEquilibration.SphericalPositivePerturbation
