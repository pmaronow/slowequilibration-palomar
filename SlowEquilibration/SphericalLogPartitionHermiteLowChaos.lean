-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalAveragedDerivativeEnergy
public import SlowEquilibration.GaussianHermiteReplicaDerivative
public import SlowEquilibration.GaussianHermiteOrderedEnergy

/-! Dimension-independent low-chaos bounds for the actual spherical log
partition, uniformly over any choice of the centering constant. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalLogPartitionHermiteLowChaos

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel GaussianSpinInterpolation GaussianReplicaDerivatives
open GaussianHermiteDerivative GaussianHermiteOrderedEnergy
open SphericalAveragedDerivativeEnergy
open OAI.MinUncut.GaussianHermite GaussianMaximalCorrelation
open scoped BigOperators Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Subtracting a constant changes only the zero Hermite coefficient. -/
theorem coeff_sub_const_of_ne_zero {ι : Type*} [Fintype ι]
    (f : (ι → ℝ) → ℝ) (hf : MemLp f 2 (γpi ι)) (m : ℝ)
    (a : ι → ℕ) (ha : a ≠ 0) :
    coeff (fun x => f x-m) a = coeff f a := by
  have hzero : (∫ x, psi a x ∂γpi ι) = 0 := by
    have h := psi_product a (0 : ι → ℕ)
    simpa [psi, H, ha] using h
  have hif : Integrable (fun x : ι → ℝ => psi a x * f x) (γpi ι) :=
    (memLp_psi a).integrable_mul hf
  have hic : Integrable (fun x : ι → ℝ => psi a x * m) (γpi ι) :=
    ((memLp_psi a).integrable (by norm_num)).mul_const m
  unfold coeff
  simp_rw [mul_sub]
  rw [integral_sub hif hic, integral_mul_const, hzero, zero_mul, sub_zero]

private theorem physical_regular {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) :
    (∀ n d, ContDiff ℝ 1
      (directionalDerivatives (logPartitionEuclidean (N := N) (mixtureCoefficients μ) β) n d)) ∧
    (∀ n d, ∃ B : ℝ≥0, LipschitzWith B
      (directionalDerivatives (logPartitionEuclidean (N := N) (mixtureCoefficients μ) β) n d)) := by
  let L := scaledLinear (sphereLinear (N := N) (mixtureCoefficients μ)) β
  let K := |β| * Real.sqrt ((N : ℝ) * covariancePolynomial (mixtureCoefficients μ) 1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hL : Measurable L := scaledLinear_measurable _ (sphereLinear_measurable _) β
  have hb : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ K :=
    scaledLinear_bound _ _ (sphereLinear_bound hN _ (mixtureCoefficients_nonnegative μ)) β
  rw [← physicalLogPartition_eq]
  exact ⟨directionalDerivatives_logPartition_contDiff (sphereLaw N) L hL hK hb,
    directionalDerivatives_logPartition_lipschitz (sphereLaw N) L hL hK hb⟩

/-- Actual product-coordinate log partitions have all the regularity
needed by the product Hermite integration-by-parts argument. -/
theorem physical_product_jets {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (n : ℕ) (d : Fin n → Coordinate N μ.maxDegree) :
    ExponentialFirstJet (mixedCoordinatePartial
      (fun x => logPartitionEuclidean (mixtureCoefficients μ) β (WithLp.toLp 2 x)) n d) :=
  mixedCoordinatePartial_euclidean_pullback_exponentialFirstJet _
    (physical_regular hN μ β).1 (physical_regular hN μ β).2 n d

/-- Every fixed positive chaos level is bounded by its actual physical
ordered derivative square energy, uniformly over the centering constant. -/
theorem finite_low_chaos_le_physical_energy {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β m : ℝ) (d : ℕ) :
    (∑' a : Coordinate N μ.maxDegree → ℕ,
      if 0 < degree a ∧ degree a < d then
        (coeff (fun x => logPartitionEuclidean (mixtureCoefficients μ) β
          (WithLp.toLp 2 x)-m) a)^2 else 0) ≤
      ∑ k ∈ Finset.Ico 1 d, averagedDerivativeSquareEnergy N μ β k := by
  classical
  let f : (Coordinate N μ.maxDegree → ℝ) → ℝ := fun x =>
    logPartitionEuclidean (mixtureCoefficients μ) β (WithLp.toLp 2 x)
  let t := Finset.Ico 1 d
  let s : Finset (Coordinate N μ.maxDegree → ℕ) := t.biUnion degreeIndices
  have hs (a : Coordinate N μ.maxDegree → ℕ) :
      a ∈ s ↔ 0 < degree a ∧ degree a < d := by
    simp [s, t, mem_degreeIndices, Nat.succ_le_iff]
  have hj := physical_product_jets hN μ β
  have hf2 : MemLp f 2 (γpi (Coordinate N μ.maxDegree)) :=
    (hj 0 Fin.elim0).memLp_two
  have htsum :
      (∑' a : Coordinate N μ.maxDegree → ℕ,
        if 0 < degree a ∧ degree a < d then
          (coeff (fun x => f x-m) a)^2 else 0) = ∑ a ∈ s, (coeff f a)^2 := by
    rw [tsum_eq_sum (s := s) (fun a ha => by
      have hnot : ¬ (0 < degree a ∧ degree a < d) := fun h => ha ((hs a).mpr h)
      simp only [hnot, ite_false])]
    apply Finset.sum_congr rfl
    intro a ha
    rw [ite_eq_left ((hs a).mp ha)]
    rw [coeff_sub_const_of_ne_zero f hf2 m a (fun he => by
      have hp := ((hs a).mp ha).1
      simp [he, degree] at hp)]
  change (∑' a, if 0 < degree a ∧ degree a < d then
    (coeff (fun x => f x-m) a)^2 else 0) ≤ _
  rw [htsum]
  have hbound := finite_coeff_sum_le_ordered_by_degree f hj
    (fun k I => (hj k I).memLp_two) s t
    (fun a ha => Finset.mem_Ico.mpr ⟨((hs a).mp ha).1, ((hs a).mp ha).2⟩)
  apply hbound.trans
  apply Finset.sum_le_sum
  intro k _
  simp_rw [f, integral_mixedCoordinatePartial_euclidean_pullback _
    (fun k I => ((physical_regular hN μ β).1 k I).differentiable (by norm_num))]
  exact le_rfl

/-- Fixed low-chaos cutoffs have dimension-independent bounds for every
finite mixture and real beta. The center may depend arbitrarily on N. -/
theorem low_chaos_eventually_bounded (μ : FiniteMixture) (β : ℝ) :
    ∃ A : ℕ → ℝ, ∀ d : ℕ, 1 ≤ d → ∀ᶠ N : ℕ in atTop, ∀ m : ℝ,
      (∑' a : Coordinate N μ.maxDegree → ℕ,
        if 0 < degree a ∧ degree a < d then
          (coeff (fun x => logPartitionEuclidean (mixtureCoefficients μ) β
            (WithLp.toLp 2 x)-m) a)^2 else 0) ≤ A d := by
  classical
  choose C hC hb using averagedDerivativeSquareEnergy_eventually_bounded μ β
  refine ⟨fun d => ∑ k ∈ Finset.Ico 1 d, C (k-1), ?_⟩
  intro d _
  have hall : ∀ᶠ N : ℕ in atTop, ∀ k ∈ Finset.Ico 1 d,
      averagedDerivativeSquareEnergy N μ β k ≤ C (k-1) := by
    apply (eventually_all_finset _).mpr
    intro k hk
    have hkpos := (Finset.mem_Ico.mp hk).1
    simpa only [show k-1+1=k by omega] using hb (k-1)
  filter_upwards [hall, eventually_ge_atTop (1 : ℕ)] with N hB hN
  intro m
  exact (finite_low_chaos_le_physical_energy hN μ β m d).trans
    (Finset.sum_le_sum fun k hk => hB k hk)

end SlowEquilibration.SphericalLogPartitionHermiteLowChaos
