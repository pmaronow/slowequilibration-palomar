-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteFiniteCoordinates
public import SlowEquilibration.SphericalInfiniteTruncation
public import SlowEquilibration.FiniteTensorMixtureMaximum

/-! The sharp aggregate Gaussian bound for literal finite sums selected from
the original infinite tensor disorder. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory Set SphericalModel
open scoped RealInnerProductSpace BigOperators
open PureTensorJetFeatures PureTensorJetBounds FiniteTensorMixtureMaximum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual physical radius, as a map from the unit sphere into the ball. -/
def unitToBall (N : ℕ) : C(UnitSphere N,PhysicalBall N) :=
  ⟨fun x => ⟨Real.sqrt N • x.val,by
      simp [Metric.mem_closedBall,dist_zero_right,norm_smul,
        abs_of_nonneg (Real.sqrt_nonneg N),unit_norm]⟩,
    by apply Continuous.subtype_mk;exact continuous_subtype_val.const_smul (Real.sqrt N)⟩

def sphereRestriction (N : ℕ) : C(PhysicalBall N,ℝ) →L[ℝ] C(UnitSphere N,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (unitToBall N)

theorem sphereRestriction_norm_le (N : ℕ) (F : C(PhysicalBall N,ℝ)) :
    ‖sphereRestriction N F‖≤‖F‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg F)).2
  intro x
  exact F.norm_coe_le_norm (unitToBall N x)

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def selectedSphereField {N : ℕ} (μ : InfiniteMixture) (p : σ → ℕ) (J : Disorder N) :
    C(UnitSphere N,ℝ) := ∑ i,sphereRestriction N (blockContinuous μ (p i) J)

def tensorSphereField {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : C(UnitSphere N,ℝ) :=
  ⟨fun x => inner ℝ (feature d c x.val) g,
    ((feature_continuous d c).comp continuous_subtype_val).inner continuous_const⟩

theorem tensorSphereField_norm {N : ℕ} (hN : 0<N) (d : σ → ℕ) (c : σ → ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    ‖tensorSphereField d c g‖=absoluteSupremum (fun x : UnitSphere N => feature d c x.val) g := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hc := (feature_continuous d c).comp (continuous_subtype_val : Continuous (fun x : UnitSphere N => x.val))
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (absoluteSupremum_nonneg _ hc g)).2
    intro x
    exact norm_inner_le_absoluteSupremum _ hc g x
  · apply ciSup_le
    intro v
    rcases v with ⟨s,x⟩
    have h := (tensorSphereField d c g).norm_coe_le_norm x
    change |inner ℝ (feature d c x.val) g|≤_ at h
    cases s
    · simpa [signedFeature,sign] using (neg_le_abs (inner ℝ (feature d c x.val) g)).trans h
    · simpa [signedFeature,sign] using (le_abs_self (inner ℝ (feature d c x.val) g)).trans h

theorem pure_physical_feature {N p : ℕ} (hN : 0<N) (hp : 1≤p)
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    SphericalAging.FiniteModel.Hamiltonian N p J (Real.sqrt N • x)=
      Real.sqrt N * ∑ I : SphericalAging.FiniteModel.TensorIndex N p,
        J I*tensorFeature (fun _ : Fin p => x) I := by
  have hn : SphericalAging.FiniteModel.normalization N p*Real.sqrt N^p=Real.sqrt N := by
    have hh := SphericalAging.LandscapeDerivatives.normalization_sqrt_power (p := p) hN
    have hpw : Real.sqrt N^p=Real.sqrt N^(p-1)*Real.sqrt N := by
      conv_lhs => rw [show p=(p-1)+1 by omega]
      rw [pow_succ]
    rw [hpw,← mul_assoc,hh,one_mul]
  unfold SphericalAging.FiniteModel.Hamiltonian SphericalAging.FiniteModel.tensorMonomial
  simp only [PiLp.smul_apply,smul_eq_mul,Finset.prod_mul_distrib,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,tensorFeature_apply]
  calc
    _ = (SphericalAging.FiniteModel.normalization N p*Real.sqrt N^p)*
      ∑ I : SphericalAging.FiniteModel.TensorIndex N p,J I*∏ k : Fin p,x (I k) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro I _
        ring
    _ = _ := by rw [hn]

theorem selectedSphereField_eq_tensorSphereField {N : ℕ} (hN : 0<N)
    (μ : InfiniteMixture) (p : σ → ℕ) (J : Disorder N) :
    selectedSphereField μ p J=tensorSphereField (fun i => p i+2)
      (fun i => μ.coeff (p i+2)) (finiteCoordinates p J) := by
  ext x
  simp only [selectedSphereField,ContinuousMap.sum_apply,sphereRestriction,
    ContinuousMap.compCLM_apply,ContinuousMap.comp_apply,blockContinuous,ContinuousMap.coe_mk,
    unitToBall,block,tensorSphereField]
  have he (i : σ) := pure_physical_feature (p := p i+2) hN (by omega) (J (p i)) x.val
  simp_rw [he]
  simp only [PiLp.inner_apply,Fintype.sum_sigma,feature_apply,finiteCoordinates,
    RCLike.inner_apply,conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

theorem selectedSphereField_expected_norm_le {N : ℕ} (hN : 0<N)
    (μ : InfiniteMixture) (p : σ → ℕ) (hp : Function.Injective p) :
    (∫ J,‖selectedSphereField μ p J‖ ∂disorderLaw N)≤
      2*N*Real.sqrt (∑ i,((p i+2:ℕ):ℝ)*μ.coeff (p i+2)) := by
  have hc := ((feature_continuous (N := N) (fun i => p i+2)
    (fun i => μ.coeff (p i+2))).comp
      (continuous_subtype_val : Continuous (fun x : UnitSphere N => x.val)))
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have he := (finiteCoordinates_hasLaw (N := N) p hp).integral_comp
    (absoluteSupremum_integrable _ hc).aestronglyMeasurable
  simp only [Function.comp_def] at he
  simp_rw [selectedSphereField_eq_tensorSphereField hN,tensorSphereField_norm hN]
  rw [he]
  exact FiniteTensorMixtureMaximum.expected_absoluteSupremum_le hN
    (fun i => p i+2) (fun i => μ.coeff (p i+2)) (fun i => μ.nonneg _) (fun i => by omega)

end SlowEquilibration.SphericalInfiniteModel
