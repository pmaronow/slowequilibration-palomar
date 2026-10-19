-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalParisiSphereNetGeometry
public import SlowEquilibration.SphericalFullFieldIdentity
public import SlowEquilibration.SphericalGuerraBound

/-! Actual ordered Gaussian row laws and a true integrable derivative
envelope for finite aggregate tensor fields, valid for every positive degree. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set Metric
open SphericalAging.FiniteModel PureTensorJetBounds PureTensorJetFeatures
open FiniteTensorMixtureMaximum
open scoped NNReal ENNReal InnerProductSpace BigOperators
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] {N : ℕ}

def rawRow (d : σ → ℕ) (i : σ) (g : EuclideanSpace ℝ (Coordinate N d)) :
    SphericalAging.FiniteModel.Disorder N (d i) := fun I => g ⟨i,I⟩

theorem rawRow_hasLaw (d : σ → ℕ) (i : σ) :
    HasLaw (rawRow (N := N) d i) (SphericalAging.FiniteModel.disorderLaw N (d i))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  have hp := SphericalModel.projectGaussian_hasLaw (fun I : TensorIndex N (d i) => (⟨i,I⟩ : Coordinate N d))
    (by intro I K h; exact eq_of_heq (Sigma.mk.inj h).2)
  have hm : Measurable (WithLp.ofLp : EuclideanSpace ℝ (TensorIndex N (d i)) →
      SphericalAging.FiniteModel.Disorder N (d i)) := by fun_prop
  have ht : Measurable (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N (d i) →
      EuclideanSpace ℝ (TensorIndex N (d i))) := by fun_prop
  have hl : HasLaw (WithLp.ofLp : EuclideanSpace ℝ (TensorIndex N (d i)) →
      SphericalAging.FiniteModel.Disorder N (d i))
      (SphericalAging.FiniteModel.disorderLaw N (d i))
      (SYK.standardGaussianMeasureOnEuclidean (TensorIndex N (d i))) := by
    refine ⟨hm.aemeasurable,?_⟩
    rw [SYK.standardGaussianMeasureOnEuclidean,Measure.map_map hm ht]
    simp only [Function.comp_def]
    change Measure.map (id : (TensorIndex N (d i) → ℝ) → (TensorIndex N (d i) → ℝ))
      (SphericalAging.FiniteModel.disorderLaw N (d i)) = SphericalAging.FiniteModel.disorderLaw N (d i)
    exact Measure.map_id
  exact hl.fun_comp hp

def derivativeEnvelope (d : σ → ℕ) (c : σ → ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : ℝ :=
  Real.sqrt (N : ℝ) * ∑ i,Real.sqrt (c i) * unitJetEnvelope N (d i) 1 (rawRow d i g)

def derivativeConstant (d : σ → ℕ) (c : σ → ℝ) : ℝ :=
  ∑ i,6 * Real.sqrt (c i) * (d i : ℝ) * Real.sqrt (d i : ℝ)

theorem derivativeConstant_nonneg (d : σ → ℕ) (c : σ → ℝ) :
    0 ≤ derivativeConstant d c := by
  unfold derivativeConstant
  exact Finset.sum_nonneg fun _ _ => by positivity

theorem derivativeEnvelope_nonneg (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ)
    (g : EuclideanSpace ℝ (Coordinate N d)) : 0 ≤ derivativeEnvelope d c g :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ =>
    mul_nonneg (Real.sqrt_nonneg _) (unitJetEnvelope_nonneg hN _))

theorem derivativeEnvelope_integrable (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ) :
    Integrable (derivativeEnvelope (N := N) d c)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  apply Integrable.const_mul
  exact integrable_finsetSum _ (fun i _ =>
    ((rawRow_hasLaw d i).integrable_comp (unitJetEnvelope_integrable hN)).const_mul _)

theorem expected_derivativeEnvelope_le (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ)
    (hd : ∀ i,1 ≤ d i) :
    (∫ g,derivativeEnvelope (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        derivativeConstant d c * (N : ℝ) := by
  have hi (i : σ) : Integrable (fun g => Real.sqrt (c i) * unitJetEnvelope N (d i) 1 (rawRow d i g))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) :=
    ((rawRow_hasLaw d i).integrable_comp (unitJetEnvelope_integrable hN)).const_mul _
  unfold derivativeEnvelope
  rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
  calc
    _ ≤ Real.sqrt (N : ℝ) * ∑ i,Real.sqrt (c i) *
        (6 * (d i : ℝ) * Real.sqrt (d i : ℝ) * Real.sqrt (N : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      apply Finset.sum_le_sum
      intro i _
      have he := (rawRow_hasLaw d i).integral_comp
        (f := unitJetEnvelope N (d i) 1) (unitJetEnvelope_continuous hN).aestronglyMeasurable
      change (∫ g,unitJetEnvelope N (d i) 1 (rawRow d i g)
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) = _ at he
      rw [integral_const_mul,he]
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      simpa only [Nat.cast_one,pow_one,show (2 : ℝ) * (1 + 2) = 6 by norm_num] using
        expected_unitJetEnvelope_le (j := 1) hN (hd i)
    _ = _ := by
      rw [derivativeConstant,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (6 * Real.sqrt (c i) * (d i : ℝ) * Real.sqrt (d i : ℝ)) * (Real.sqrt (N : ℝ))^2 := by ring
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

theorem pure_scaled_increment_le (hN : 0 < N) (p : ℕ)
    (J : SphericalAging.FiniteModel.Disorder N p) (x y : UnitSphere N) :
    |Hamiltonian N p J (Real.sqrt (N : ℝ) • x.val) -
      Hamiltonian N p J (Real.sqrt (N : ℝ) • y.val)| ≤
        Real.sqrt (N : ℝ) * unitJetEnvelope N p 1 J * ‖x.val - y.val‖ := by
  have hdiff := (Hamiltonian_contDiff J).differentiable (by simp)
  have hb (z : Vector N) (hz : z ∈ closedBall (0 : Vector N) (Real.sqrt (N : ℝ))) :
      ‖fderiv ℝ (Hamiltonian N p J) z‖ ≤ unitJetEnvelope N p 1 J := by
    have h := iteratedFDeriv_norm_le_pureJetEnvelope (j := 1) hN J z
      (by simpa only [mem_closedBall,dist_zero_right] using hz)
    simpa only [norm_iteratedFDeriv_one,pureJetEnvelope,SphericalAging.LandscapeDerivatives.normalization_sqrt_power hN,one_mul] using h
  have hx : Real.sqrt (N : ℝ) • x.val ∈ closedBall (0 : Vector N) (Real.sqrt (N : ℝ)) := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),unit_norm,mul_one,le_refl]
  have hy : Real.sqrt (N : ℝ) • y.val ∈ closedBall (0 : Vector N) (Real.sqrt (N : ℝ)) := by
    simp only [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),unit_norm,mul_one,le_refl]
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z) hb
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))) hy hx
  simpa only [Real.norm_eq_abs,← smul_sub,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),mul_left_comm,mul_assoc] using h

end SlowEquilibration.SphericalParisiSphereNet
