-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUniformPowerBudget
public import SlowEquilibration.GaussianGGUniformFiniteTests

/-! Genuine finite Gaussian tensor positivity, uniform over dimensions
and arbitrary ordinary unit-sphere Gibbs base measures. Every input to
the finite GG consumer is supplied by the actual perturbation model. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianGGEnsemble GaussianGGCutoffs GaussianPerturbationDeviation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal overlap law of two independent replicas under the true
finite tensor Gibbs law, averaged over independent normalized positive
parameters and actual iid Gaussian tensor disorder. -/
def perturbedOverlapLaw {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    (v : ℝ) : Measure ℝ :=
  overlapFamily (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
    (ambientParameterizedGibbsKernel ν v) ∘ₘ positiveCubeLaw K

theorem perturbedOverlapLaw_probability {N K : ℕ} (ν : Measure (UnitSpin N))
    [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v) :
    IsProbabilityMeasure (perturbedOverlapLaw (K := K) ν v) := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  unfold perturbedOverlapLaw
  infer_instance

theorem perturbedOverlapLaw_negative_mass {N K : ℕ} (ν : Measure (UnitSpin N))
    [IsProbabilityMeasure ν] {v : ℝ} (hv : 0≤v) (ε : ℝ) :
    (perturbedOverlapLaw (K := K) ν v).real (Iic (-ε))=
      ∫x,starMass (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
        ((ambientParameterizedGibbsKernel ν v).sectR x) ε 1 ∂positiveCubeLaw K := by
  let _ := ambientParameterizedGibbsKernel_markov (K := K) ν hv
  rw [perturbedOverlapLaw,kernel_real_mean _ _ _ measurableSet_Iic]
  apply integral_congr_ae
  exact .of_forall fun x => by
    change ((overlapFamily (SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K))
      (ambientParameterizedGibbsKernel ν v)) x).real (Iic (-ε))=_
    rw [overlapFamily_apply]
    exact (starMass_one _ _ ε).symm

/-- Uniform Talagrand positivity for the genuine finite spherical tensor
perturbation. Its degree count and strength threshold are selected before
all dimensions and all underlying probability measures. No GG identities,
smallness, or positivity conclusion is an input. -/
theorem exists_uniform_perturbation_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ, ∃ V : ℝ, 0<K ∧ 1≤V ∧
      ∀ {N : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
        (v : ℝ), V≤v → (perturbedOverlapLaw (K := K) ν v).real (Iic (-ε))≤η := by
  obtain ⟨n,M,k,C,hn,hM,hC,hFinite⟩ :=
    exists_uniform_finite_power_bound hε hε1 (by positivity : 0<η/2)
  let Q : ℝ := ∑m∈Finset.Ico 1 n, ∑j : Fin M, ∑p∈Finset.range (k+1), (1:ℝ)
  have hQ : 0≤Q := by dsimp [Q];positivity
  let δ : ℝ := η/(2*C*(Q+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  have hδeq : 2*C*(Q+1)*δ=η := by
    dsimp [δ]
    field_simp
  obtain ⟨V,hV1,hPower⟩ := exists_uniform_cube_power_threshold (k+1) hδ
  refine ⟨k+1,V,by omega,hV1,?_⟩
  intro N ν _ v hV
  have hv : 0<v := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (hV1.trans hV)
  let d := SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N (k+1))
  let G := ambientParameterizedGibbsKernel (K := k+1) ν v
  let _ : IsMarkovKernel G := ambientParameterizedGibbsKernel_markov ν hv.le
  have hG : ∀ᵐ x ∂positiveCubeLaw (k+1), ∀ᵐ w ∂d, ∀ᵐ z ∂G (x,w), ‖z‖≤1 :=
    .of_forall fun x => .of_forall fun w =>
      (ambientParameterizedGibbsKernel_unit_support ν v (x,w)).mono fun z hz => hz.le
  have hFin := hFinite (Fin (k+1) → ℝ) (PerturbationDisorder N (k+1)) (Vector N)
    (positiveCubeLaw (k+1)) d G hG
  have hEach (m : ℕ) (j : Fin M) (p : ℕ) (hp : p∈Finset.range (k+1)) :
      cubeMeanPowerDefect (K := k+1) ν v (-leftEndpoint ε M j) m p≤δ := by
    by_cases hp0 : p=0
    · subst p
      rw [cubeMeanPowerDefect_zero ν hv.le]
      exact hδ.le
    · let q : Fin (k+1) := ⟨p-1,by have := Finset.mem_range.mp hp;omega⟩
      have hq : q.val+1=p := by dsimp [q];omega
      simpa only [hq] using hPower ν v hV q (-leftEndpoint ε M j) m
  have hErr : finitePowerError (positiveCubeLaw (k+1)) d G ε n M k≤Q*δ := by
    unfold finitePowerError
    calc
      _ ≤ ∑m∈Finset.Ico 1 n, ∑j : Fin M, ∑p∈Finset.range (k+1), δ := by
        apply Finset.sum_le_sum
        intro m hm
        apply Finset.sum_le_sum
        intro j hj
        apply Finset.sum_le_sum
        intro p hp
        exact hEach m j p hp
      _ = Q*δ := by dsimp [Q];simp only [Finset.sum_mul,one_mul]
  have hsmall : C*(Q*δ)≤η/2 := by
    have hnon : 0≤C*δ := by positivity
    nlinarith [hδeq]
  rw [perturbedOverlapLaw_negative_mass ν hv.le]
  change (∫x,starMass d (G.sectR x) ε 1 ∂positiveCubeLaw (k+1))≤η
  calc
    _ ≤ η/2+C*finitePowerError (positiveCubeLaw (k+1)) d G ε n M k := hFin
    _ ≤ η/2+C*(Q*δ) := add_le_add (le_refl (η/2)) (mul_le_mul_of_nonneg_left hErr hC.le)
    _ ≤ η := by linarith

end SlowEquilibration.SphericalPositivePerturbation
