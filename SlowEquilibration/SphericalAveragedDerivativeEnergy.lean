-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTensorDerivativeNormalization
public import SlowEquilibration.SphericalIndependentReplicaMoments
public import SlowEquilibration.OrderedSigmaTensor

/-! Dimension-independent fixed-order squared energy of the averaged
actual disorder derivatives. The finite Gibbs derivative expansion and
independent-copy tensor contraction supply every probabilistic input.
-/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalAveragedDerivativeEnergy

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel GaussianSpinInterpolation GaussianReplicaCalculus
open GaussianReplicaDerivatives SphericalTensorDerivativeNormalization
open SphericalAnnealedGibbs SphericalIndependentReplicaMoments OrderedSigmaTensor
open IndependentReplicaTensorContraction
open scoped BigOperators Topology NNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.unusedSectionVars false

/-- The bounded linear-feature log partition is the literal physical one. -/
theorem physicalLogPartition_eq {N P : ℕ} (c : Degree P → ℝ) (β : ℝ) :
    logPartition (sphereLaw N) (scaledLinear (sphereLinear c) β) =
      logPartitionEuclidean (N := N) c β := by
  funext w
  unfold logPartition GaussianSpinInterpolation.moment weight logPartitionEuclidean partition
  simp only [scaledLinear, smul_apply, smul_eq_mul, one_mul, sphereLinear_apply]

private theorem physicalGibbs_eq {N : ℕ} (μ : FiniteMixture) (β : ℝ)
    (w : EuclideanDisorder N μ.maxDegree) :
    gibbsMeasure (sphereLaw N) (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β) w =
      mixtureGibbsLaw μ β (unpackDisorder w) := by
  have he : gibbsMeasure (sphereLaw N)
      (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β) w =
      gibbsMeasure (sphereLaw N) (sphereLinear (N := N) (mixtureCoefficients μ)) (β • w) := by
    unfold gibbsMeasure
    simp only [GaussianSpinInterpolation.moment, weight, scaledLinear, smul_apply, map_smul, smul_eq_mul]
  exact he.trans (gaussianGibbs_eq_gibbsLaw (mixtureCoefficients μ) β w)

private theorem physicalFeatureBound {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    ∀ᵐ x ∂sphereLaw N,
      ‖scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β x‖ ≤
        |β| * Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1) :=
  scaledLinear_bound _ _ (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)) β

/-- Every feature monomial in the derivative expansion is integrable under
the actual original-disorder replica law. -/
theorem annealed_featureMonomial_integrable {N r k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (labels : Fin k → Fin r)
    (d : Fin k → EuclideanDisorder N μ.maxDegree) :
    Integrable (featureMonomial (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β)
      labels d) (annealedReplicaLaw hN μ β r) := by
  let L := scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1)
  have hall : ∀ᵐ σ ∂annealedReplicaLaw hN μ β r,
      ∀ j : Fin k, ‖L (σ (labels j))‖ ≤ K := by
    apply ae_all_iff.mpr
    intro j
    exact ((annealedReplica_eval_hasLaw hN μ β (labels j)).measurePreserving
      (measurable_pi_apply (labels j))).quasiMeasurePreserving.ae (physicalFeatureBound hN μ β)
  apply Integrable.of_bound
    (featureMonomial_measurable L (scaledLinear_measurable _ (sphereLinear_measurable _) β)
      labels d).aestronglyMeasurable (∏ j, K * ‖d j‖)
  filter_upwards [hall] with σ hσ
  rw [Real.norm_eq_abs, featureMonomial, Finset.abs_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ =>
    (L (σ (labels j))).le_opNorm (d j) |>.trans
      (mul_le_mul_of_nonneg_right (hσ j) (norm_nonneg _))

/-- Averaging the genuine Gaussian feature-monomial expectation gives the
literal original-disorder annealed replica integral. -/
theorem integral_replica_featureMonomial {N r k : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (labels : Fin k → Fin r)
    (d : Fin k → EuclideanDisorder N μ.maxDegree) :
    (∫ w, replicaExpectation (sphereLaw N)
      (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β) r
        (featureMonomial (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β) labels d) w
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) =
    ∫ σ, featureMonomial (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β) labels d σ
      ∂annealedReplicaLaw hN μ β r := by
  let L := scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := scaledLinear_measurable _ (sphereLinear_measurable _) β
  have hb : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ K := physicalFeatureBound hN μ β
  have hf := featureMonomial_measurable L hL labels d
  have hfb := featureMonomial_bound (sphereLaw N) L hK hb labels d
  have hm : AEStronglyMeasurable
      (replicaExpectation (sphereLaw N) L r (featureMonomial L labels d))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    (replicaExpectation_contDiff (sphereLaw N) L hL hK
    (show 0 ≤ ∏ j, K * ‖d j‖ by positivity) hb r _ hf hfb).continuous.aestronglyMeasurable
  rw [← (euclideanDisorder_hasLaw N μ.maxDegree).integral_comp hm]
  rw [integral_annealedReplicaLaw hN μ β _ (annealed_featureMonomial_integrable hN μ β labels d)]
  apply integral_congr_ae
  exact .of_forall fun J => by
    unfold replicaExpectation
    dsimp only [Function.comp_def, L]
    rw [physicalGibbs_eq, unpack_euclideanDisorder]

/-- The averaged actual physical derivative is a finite combination of
original-disorder annealed replica monomials. -/
theorem averaged_directionalDerivative_expansion {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (n : ℕ)
    (d : Fin (n+1) → EuclideanDisorder N μ.maxDegree) :
    (∫ w, directionalDerivatives (logPartitionEuclidean (mixtureCoefficients μ) β)
      (n+1) d w ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) =
    ∑ t : ExpansionIndex n, expansionCoefficient n t *
      ∫ σ, featureMonomial (scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β)
        (expansionLabels n t) d σ ∂annealedReplicaLaw hN μ β (n+1) := by
  let L := scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := scaledLinear_measurable _ (sphereLinear_measurable _) β
  have hb : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ K := physicalFeatureBound hN μ β
  have hf (t : ExpansionIndex n) := featureMonomial_measurable L hL (expansionLabels n t) d
  have hfb (t : ExpansionIndex n) :=
    featureMonomial_bound (sphereLaw N) L hK hb (expansionLabels n t) d
  have hi (t : ExpansionIndex n) : Integrable
      (replicaExpectation (sphereLaw N) L (n+1) (featureMonomial L (expansionLabels n t) d))
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) :=
    replicaExpectation_gaussian_integrable (sphereLaw N) L hL hK
      (show 0 ≤ ∏ j, K * ‖d j‖ by positivity) hb (n+1) _ (hf t) (hfb t)
  rw [← physicalLogPartition_eq]
  have heq := funext (directionalDerivatives_logPartition_expansion (sphereLaw N) L hL hK hb n d)
  rw [heq, integral_finsetSum _ (fun t _ => (hi t).const_mul _)]
  apply Finset.sum_congr rfl
  intro t _
  rw [integral_const_mul, integral_replica_featureMonomial hN μ β]

/-- The actual sum of squared Gaussian-averaged kth disorder derivatives,
over every ordered coordinate tuple, including repetitions. -/
def averagedDerivativeSquareEnergy (N : ℕ) (μ : FiniteMixture) (β : ℝ) (k : ℕ) : ℝ :=
  ∑ I : Fin k → Coordinate N μ.maxDegree,
    (∫ w, directionalDerivatives (logPartitionEuclidean (mixtureCoefficients μ) β) k
      (fun j => EuclideanSpace.single (I j) 1) w
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) ^ 2

/-- Exact physical normalization of the averaged derivative in a fixed
sequence of ordered tensor degrees. -/
theorem averaged_coordinateDerivative_expansion {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) (p : Fin (n+1) → Degree μ.maxDegree)
    (I : (j : Fin (n+1)) → SphericalAging.FiniteModel.TensorIndex N (p j).val.val) :
    (∫ w, directionalDerivatives (logPartitionEuclidean (mixtureCoefficients μ) β)
      (n+1) (fun j => EuclideanSpace.single ⟨p j, I j⟩ 1) w
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) =
    tensorDerivativeAmplitude N (mixtureCoefficients μ) β p *
      ∑ t : ExpansionIndex n, expansionCoefficient n t *
        ∫ σ : Fin (n+1) → Vector N,
          replicaMonomial (flattenedReplicaLabels p (expansionLabels n t))
            (fun a i => σ a i) (flattenedTensorIndex p I)
          ∂annealedReplicaLaw hN μ β (n+1) := by
  rw [averaged_directionalDerivative_expansion hN μ β]
  simp_rw [featureMonomial_eq_amplitude_mul_replicaMonomial, integral_const_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- At every fixed physical-degree pattern the full ordered derivative
square sum is bounded by a dimension-independent constant. -/
theorem fixed_degree_pattern_eventually_bounded (μ : FiniteMixture) (β : ℝ)
    (n : ℕ) (p : Fin (n+1) → Degree μ.maxDegree) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ hN : 1 ≤ N,
      (∑ I : (j : Fin (n+1)) → SphericalAging.FiniteModel.TensorIndex N (p j).val.val,
        (∫ w, directionalDerivatives (logPartitionEuclidean (mixtureCoefficients μ) β)
          (n+1) (fun j => EuclideanSpace.single ⟨p j, I j⟩ 1) w
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) ^ 2) ≤ C := by
  classical
  let α := TensorSlots p
  have hcard : Fintype.card α = totalTensorDegree p := by
    simp [α, TensorSlots, totalTensorDegree, Fintype.card_sigma]
  have hdegree : 2 * (n+1) ≤ Fintype.card α :=
    hcard.symm ▸ twice_order_le_totalTensorDegree p
  letI : Nonempty α := by
    apply Fintype.card_pos_iff.mp
    omega
  obtain ⟨C, hC, hraw⟩ := normalized_replica_tensor_mean_square_eventually_bounded_of_fintype
    α (n+1) hdegree
  let A : ℝ := ∏ j, β ^ 2 * mixtureCoefficients μ (p j)
  let D : ℝ := (Fintype.card (ExpansionIndex n) : ℝ) *
    ∑ t : ExpansionIndex n, expansionCoefficient n t ^ 2
  have hA : 0 ≤ A := Finset.prod_nonneg fun j _ =>
    mul_nonneg (sq_nonneg _) (mixtureCoefficients_nonnegative μ _)
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  refine ⟨D * A * C + 1, by positivity, ?_⟩
  filter_upwards [hraw] with N hraw
  intro hN
  let R : ℝ := (N : ℝ) ^ (-((totalTensorDegree p - (n+1) : ℕ) : ℝ))
  let b : ExpansionIndex n → (α → Fin N) → ℝ := fun t I =>
    ∫ σ : Fin (n+1) → Vector N,
      replicaMonomial (flattenedReplicaLabels p (expansionLabels n t))
        (fun a i => σ a i) I ∂annealedReplicaLaw hN μ β (n+1)
  have hb (t : ExpansionIndex n) : R * (∑ I : α → Fin N, b t I ^ 2) ≤ C := by
    simpa only [R, b, hcard] using hraw hN μ β (n+1)
      (flattenedReplicaLabels p (expansionLabels n t))
  have hweight := weighted_expansion_square_sum_le (expansionCoefficient n) b
    (show 0 ≤ R by dsimp [R]; positivity) hb
  have hsum :
      (∑ I : (j : Fin (n+1)) → SphericalAging.FiniteModel.TensorIndex N (p j).val.val,
        (∫ w, directionalDerivatives (logPartitionEuclidean (mixtureCoefficients μ) β)
          (n+1) (fun j => EuclideanSpace.single ⟨p j, I j⟩ 1) w
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N μ.maxDegree)) ^ 2) =
      tensorDerivativeAmplitude N (mixtureCoefficients μ) β p ^ 2 *
        ∑ I : α → Fin N, (∑ t : ExpansionIndex n, expansionCoefficient n t * b t I) ^ 2 := by
    rw [Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.piCurry (fun (j : Fin (n+1)) (_ : Fin (p j).val.val) => Fin N)).symm
    intro I
    rw [averaged_coordinateDerivative_expansion hN μ β, mul_pow]
    rfl
  rw [hsum, tensorDerivativeAmplitude_sq hN _ (mixtureCoefficients_nonnegative μ) β p]
  change A * R * (∑ I : α → Fin N, (∑ t : ExpansionIndex n,
    expansionCoefficient n t * b t I) ^ 2) ≤ D * A * C + 1
  calc
    _ = A * (R * ∑ I : α → Fin N, (∑ t : ExpansionIndex n,
      expansionCoefficient n t * b t I) ^ 2) := by ring
    _ ≤ A * (D * C) := mul_le_mul_of_nonneg_left hweight hA
    _ ≤ D * A * C + 1 := by nlinarith

/-- Every positive fixed order has bounded averaged derivative square
energy, for every finite mixture and every real beta. The degree-block
partition is finite and does not depend on N. -/
theorem averagedDerivativeSquareEnergy_eventually_bounded
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      averagedDerivativeSquareEnergy N μ β (n+1) ≤ C := by
  classical
  choose C hC hbound using fixed_degree_pattern_eventually_bounded μ β n
  refine ⟨(∑ p : Fin (n+1) → Degree μ.maxDegree, C p) + 1, ?_, ?_⟩
  · have hnonneg : 0 ≤ ∑ p : Fin (n+1) → Degree μ.maxDegree, C p :=
      Finset.sum_nonneg fun p _ => (hC p).le
    linarith
  · filter_upwards [eventually_all.mpr hbound, eventually_ge_atTop (1 : ℕ)] with N hb hN
    unfold averagedDerivativeSquareEnergy
    rw [sum_degree_blocks (fun p : Degree μ.maxDegree =>
      SphericalAging.FiniteModel.TensorIndex N p.val.val)]
    exact (Finset.sum_le_sum fun p _ => hb p hN).trans (by linarith)

end SlowEquilibration.SphericalAveragedDerivativeEnergy
