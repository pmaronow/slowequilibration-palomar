-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.DirectingPhysicalOrigin
public import SlowEquilibration.DirectingPhysicalRandomExclusion
public import SlowEquilibration.MixtureSubcriticalQuadratic

/-! The complete directing-norm implication of manuscript Theorem 6.3
for a measurable random directing measure, from its explicit preceding
thermal and weak-limit inputs. The squared-norm conclusion is not an
input. Physical derivation of those inputs from strict 1RSB, and the
Dovbysh--Sudakov existence/weak-limit bridge, are separate obligations. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.DirectingPhysical

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open GaussianReplicaKernel GaussianGGEnsemble

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {Ω H : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Genuine Cauchy--Schwarz support consequence for the actual overlap
law. It accommodates a positive mass at zero at this stage. -/
theorem overlapLaw_ae_abs_le_of_norm_sq_le (d : Measure Ω)
    (G : Kernel Ω H) [IsMarkovKernel G] {Q : ℝ} (hQ : 0 ≤ Q)
    (hG : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 ≤ Q) :
    ∀ᵐ r ∂overlapLaw d G, |r| ≤ Q := by
  apply Measure.ae_comp_of_ae_ae
    (show MeasurableSet {r : ℝ | |r| ≤ Q} from isClosed_le continuous_abs continuous_const |>.measurableSet)
  filter_upwards [hG] with ω hω
  rw [overlapKernel, Kernel.map_apply _ overlap_map_measurable, Kernel.prod_apply]
  apply (ae_map_iff overlap_map_measurable.aemeasurable
    (isClosed_le continuous_abs continuous_const).measurableSet).mpr
  apply (Measure.ae_prod_iff_ae_ae
    ((isClosed_le (continuous_fst.inner continuous_snd).abs continuous_const).measurableSet)).mpr
  filter_upwards [hω] with v hv
  filter_upwards [hω] with w hw
  have hvnorm : ‖v‖ ≤ Real.sqrt Q := by nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg Q, norm_nonneg v]
  have hwnorm : ‖w‖ ≤ Real.sqrt Q := by nlinarith [Real.sq_sqrt hQ, Real.sqrt_nonneg Q, norm_nonneg w]
  calc
    |inner ℝ v w| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm _ _
    _ ≤ Real.sqrt Q * Real.sqrt Q :=
      mul_le_mul hvnorm hwnorm (norm_nonneg w) (Real.sqrt_nonneg Q)
    _ = Q := Real.mul_self_sqrt hQ

/-- Absolute covariance bound for arbitrary parity. It is a direct
coefficient-wise estimate of the actual finite mixture polynomial. -/
theorem finiteMixture_xi_abs_le (ξ : FiniteMixture) {r Q : ℝ}
    (_hQ : 0 ≤ Q) (hr : |r| ≤ Q) : |ξ.xi r| ≤ ξ.xi Q := by
  apply (ξ.xi_abs_le r).trans
  unfold FiniteMixture.xi
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg r) hr p) (ξ.nonneg p)

/-- Complete mathematical norm-support conclusion, for the true IID
law of a random directing measure, from the source proof's preceding
inputs. Both even and odd finite mixtures are covered. -/
theorem directing_norm_Q_of_source_inputs (d : Measure Ω) [IsProbabilityMeasure d]
    (G : Kernel Ω H) [IsMarkovKernel G] (ξ : FiniteMixture)
    {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hball : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ≤ 1)
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ law d G k (equilateralEvent (H := H) k q ρ) = 0)
    (hcap : ∃ a < (1 : ℝ), law d G 2 (pairCapEvent (H := H) a) = 0)
    (hGG : CovarianceGG d G ξ.xi)
    (hmean : (∫ r, ξ.xi r ∂overlapLaw d G) = (1 - x) * ξ.xi Q) :
    ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 = Q := by
  have hψ : Continuous ξ.xi := continuous_iff_continuousAt.mpr fun r =>
    (ξ.hasDerivAt_xi r).continuousAt
  have htwo := directing_norms_ae_mem_of_annealed_replica_exclusion d G
    ({0, Q} : Set ℝ) (by simp) hball
    (fun q hq hqA => hexclude q hq (by intro heq; exact hqA (by simp [heq]))) hcap
  have hnormle : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ^ 2 ≤ Q := by
    filter_upwards [htwo] with ω hω
    filter_upwards [hω] with v hv
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hv) with h0 | hq
    · exact h0 ▸ hQ.1.le
    · exact hq.le
  have hpair := overlapLaw_ae_abs_le_of_norm_sq_le d G hQ.1.le hnormle
  have hupper : ∀ᵐ r ∂overlapLaw d G, ξ.xi r ≤ ξ.xi Q :=
    hpair.mono fun r hr => (le_abs_self _).trans (finiteMixture_xi_abs_le ξ hQ.1.le hr)
  have hmeanpos : 0 < ∫ r, ξ.xi r ∂overlapLaw d G := by
    rw [hmean]
    exact mul_pos (sub_pos.mpr hx.2) (ξ.xi_pos hQ.1)
  have hzero := origin_ae_zero_of_covarianceGG d G hψ ξ.xi_zero hball
    (D := ξ.xi 1) (C := ξ.xi Q)
    (fun r hr => finiteMixture_xi_abs_le ξ (by norm_num) (abs_le.mpr hr))
    (ξ.xi_pos hQ.1) hupper hmeanpos hGG
  filter_upwards [htwo, hzero] with ω hω hωzero
  have hnzero : ∀ᵐ v ∂G ω, v ≠ 0 := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hωzero
  filter_upwards [hω, hnzero] with v hv hvne
  rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hv) with h0 | hq
  · exact False.elim (hvne (norm_eq_zero.mp (sq_eq_zero_iff.mp h0)))
  · exact hq

/-- The conditional directing law places full mass on the literal
squared-norm-Q sphere. This is the manuscript's measure formulation. -/
theorem directing_sphere_mass_one_of_source_inputs (d : Measure Ω)
    [IsProbabilityMeasure d] (G : Kernel Ω H) [IsMarkovKernel G] (ξ : FiniteMixture)
    {x Q : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hball : ∀ᵐ ω ∂d, ∀ᵐ v ∂G ω, ‖v‖ ≤ 1)
    (hexclude : ∀ q ∈ Ioo (0 : ℝ) 1, q ≠ Q →
      ∃ k : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ law d G k (equilateralEvent (H := H) k q ρ) = 0)
    (hcap : ∃ a < (1 : ℝ), law d G 2 (pairCapEvent (H := H) a) = 0)
    (hGG : CovarianceGG d G ξ.xi)
    (hmean : (∫ r, ξ.xi r ∂overlapLaw d G) = (1 - x) * ξ.xi Q) :
    ∀ᵐ ω ∂d, G ω {v | ‖v‖ ^ 2 = Q} = 1 := by
  have h := directing_norm_Q_of_source_inputs d G ξ hx hQ hball hexclude hcap hGG hmean
  filter_upwards [h] with ω hω
  exact (mem_ae_iff_prob_eq_one
    (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet).mp hω

end SlowEquilibration.DirectingPhysical
