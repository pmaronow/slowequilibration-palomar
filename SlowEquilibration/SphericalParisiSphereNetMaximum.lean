-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalParisiSphereNetEnvelope
public import SlowEquilibration.SphericalParisiGaussianREMJensen

/-! Genuine finite-net approximation of the original Gaussian tensor
sphere maximum, using its actual integrable Gaussian derivative envelope. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiSphereNet
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel PureTensorJetBounds PureTensorJetFeatures
open FiniteTensorMixtureMaximum SphericalParisiGroundRSUpper
open scoped NNReal ENNReal InnerProductSpace BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {N k : ℕ}

theorem pure_Hamiltonian_scaled (hN : 0 < N) {p : ℕ} (hp : 1 ≤ p)
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    Hamiltonian N p J (Real.sqrt (N : ℝ) • x) =
      Real.sqrt (N : ℝ) * ∑ I,J I * tensorMonomial x I := by
  have hs : normalization N p * (Real.sqrt (N : ℝ))^p = Real.sqrt (N : ℝ) := by
    calc
      _ = (normalization N p * (Real.sqrt (N : ℝ))^(p - 1)) * Real.sqrt (N : ℝ) := by
        rw [mul_assoc,← pow_succ,show p - 1 + 1 = p by omega]
      _ = _ := by rw [SphericalAging.LandscapeDerivatives.normalization_sqrt_power hN,one_mul]
  simp only [Hamiltonian,SphericalEffectiveField.tensorMonomial_smul]
  simp_rw [show ∀ I : TensorIndex N p,J I * ((Real.sqrt (N : ℝ))^p * tensorMonomial x I) =
      (Real.sqrt (N : ℝ))^p * (J I * tensorMonomial x I) from fun I => by ring]
  rw [← Finset.mul_sum,← mul_assoc,hs]

omit [DecidableEq σ] in
theorem original_field_eq_sum_scaledHamiltonians (hN : 0 < N) (d : σ → ℕ)
    (c : σ → ℝ) (hd : ∀ i,1 ≤ d i) (x : Vector N)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    inner ℝ (feature d c x) g = ∑ i,Real.sqrt (c i) *
      Hamiltonian N (d i) (rawRow d i g) (Real.sqrt (N : ℝ) • x) := by
  simp only [PiLp.inner_apply,Fintype.sum_sigma,feature_apply,RCLike.inner_apply,conj_trivial]
  apply Finset.sum_congr rfl
  intro i _
  rw [pure_Hamiltonian_scaled hN (hd i),Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  simp only [rawRow,tensorMonomial,tensorFeature_apply]
  ring

omit [DecidableEq σ] in
theorem original_field_increment_le (hN : 0 < N) (d : σ → ℕ) (c : σ → ℝ)
    (hd : ∀ i,1 ≤ d i) (g : EuclideanSpace ℝ (Coordinate N d)) (x y : UnitSphere N) :
    |inner ℝ (feature d c x.val) g - inner ℝ (feature d c y.val) g| ≤
      derivativeEnvelope d c g * ‖x.val - y.val‖ := by
  rw [original_field_eq_sum_scaledHamiltonians hN d c hd,
    original_field_eq_sum_scaledHamiltonians hN d c hd,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i,|Real.sqrt (c i) * Hamiltonian N (d i) (rawRow d i g) (Real.sqrt (N : ℝ) • x.val) -
        Real.sqrt (c i) * Hamiltonian N (d i) (rawRow d i g) (Real.sqrt (N : ℝ) • y.val)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i,Real.sqrt (c i) *
        (Real.sqrt (N : ℝ) * unitJetEnvelope N (d i) 1 (rawRow d i g) * ‖x.val - y.val‖) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← mul_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (pure_scaled_increment_le hN (d i) (rawRow d i g) x y) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [derivativeEnvelope,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

def netMaximum (d : σ → ℕ) (c : σ → ℝ) (points : Fin k → UnitSphere N)
    (g : EuclideanSpace ℝ (Coordinate N d)) : ℝ :=
  ⨆ j,inner ℝ (feature d c (points j).val) g

theorem netMaximum_integrable (hk : 0 < k) (d : σ → ℕ) (c : σ → ℝ)
    (points : Fin k → UnitSphere N) :
    Integrable (netMaximum d c points)
      (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) := by
  let : NeZero k := ⟨hk.ne'⟩
  exact supremum_integrable_of_continuous (fun j : Fin k => innerSL ℝ (feature d c (points j).val))
    (continuous_of_discreteTopology : Continuous (fun j : Fin k => innerSL ℝ (feature d c (points j).val)))

omit [DecidableEq σ] in
theorem originalMaximum_le_netMaximum_add_envelope (hN : 0 < N) (hk : 0 < k)
    (d : σ → ℕ) (c : σ → ℝ) (hd : ∀ i,1 ≤ d i)
    (points : Fin k → UnitSphere N) {ε : ℝ}
    (hcover : ∀ x : UnitSphere N,∃ j,‖x.val - (points j).val‖ ≤ ε)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    actualMaximum d c g ≤ netMaximum d c points g + ε * derivativeEnvelope d c g := by
  let : NeZero N := ⟨hN.ne'⟩
  let : NeZero k := ⟨hk.ne'⟩
  apply ciSup_le
  intro x
  obtain ⟨j,hj⟩ := hcover x
  have h := (original_field_increment_le hN d c hd g x (points j)).trans
    (mul_le_mul_of_nonneg_left hj (derivativeEnvelope_nonneg hN d c g))
  have hm : inner ℝ (feature d c (points j).val) g ≤ netMaximum d c points g :=
    le_ciSup (Set.finite_range (fun l : Fin k => inner ℝ (feature d c (points l).val) g)).bddAbove j
  linarith [le_abs_self (inner ℝ (feature d c x.val) g - inner ℝ (feature d c (points j).val) g)]

theorem expected_originalMaximum_le_netMaximum (hN : 0 < N) (hk : 0 < k)
    (d : σ → ℕ) (c : σ → ℝ) (hd : ∀ i,1 ≤ d i)
    (points : Fin k → UnitSphere N) {ε : ℝ} (hε : 0 ≤ ε)
    (hcover : ∀ x : UnitSphere N,∃ j,‖x.val - (points j).val‖ ≤ ε) :
    (∫ g,actualMaximum (N := N) d c g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      (∫ g,netMaximum d c points g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) +
        derivativeConstant d c * ε * (N : ℝ) := by
  have hn := netMaximum_integrable hk d c points
  have he := (derivativeEnvelope_integrable hN d c).const_mul ε
  have h := integral_mono (actualMaximum_integrable hN d c) (hn.add he)
    (originalMaximum_le_netMaximum_add_envelope hN hk d c hd points hcover)
  simp only [Pi.add_apply] at h
  rw [integral_add hn he,integral_const_mul] at h
  have hb := mul_le_mul_of_nonneg_left (expected_derivativeEnvelope_le hN d c hd) hε
  exact h.trans (add_le_add le_rfl (hb.trans_eq (by ring)))

theorem exists_actual_unitSphere_net_expected_maximum (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hd : ∀ i,1 ≤ d i) {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (points : Fin k → UnitSphere N),0 < k ∧
      (∀ x : UnitSphere N,∃ j,‖x.val - (points j).val‖ ≤ ε) ∧
      Real.log (k : ℝ) ≤ (N : ℝ) * Real.log (1 + 2 / ε) ∧
      (∫ g,actualMaximum (N := N) d c g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        (∫ g,netMaximum d c points g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) +
          derivativeConstant d c * ε * (N : ℝ) := by
  obtain ⟨k,points,hk,hcover,hcard⟩ := exists_unitSphere_net hN hε
  exact ⟨k,points,hk,hcover,hcard,expected_originalMaximum_le_netMaximum hN hk d c hd points hε.le hcover⟩

end SlowEquilibration.SphericalParisiSphereNet
