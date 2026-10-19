-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSpinCorrelation
public import SlowEquilibration.SphericalCapMass

/-! Actual replica mass controls actual spin magnetization by ordinary
Fubini on the genuine sphere-supported probability law. -/

@[expose] public section

noncomputable section
namespace SlowEquilibration.SphericalReplicaMagnetization

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalBarycenter SphericalCenteredObservables
open scoped Topology InnerProductSpace

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

theorem norm_mean_spin_sq_eq_replica_overlap (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ x ∂π, ‖x‖^2 = (N : ℝ)) :
    ‖∫ x, spin x ∂π‖^2 = ∫ z : Vector N × Vector N, overlap z.1 z.2 ∂π.prod π := by
  have hi := integrable_sphereSupported_continuous π hπ spin_contDiff.continuous
  have he := integral_prod_bilin (innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) hi hi
  change (∫ z : Vector N × Vector N, inner ℝ (spin z.1) (spin z.2) ∂π.prod π) =
    inner ℝ (∫ x, spin x ∂π) (∫ x, spin x ∂π) at he
  simp_rw [spin_inner hN] at he
  rw [real_inner_self_eq_norm_sq] at he
  exact he.symm

/-- The exact magnetization reduction underlying `cor:pr-cap`; the
ordinary replica probability is on the actual law, not a finite surrogate. -/
theorem norm_mean_spin_sq_le (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ x ∂π, ‖x‖^2 = (N : ℝ)) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖∫ x, spin x ∂π‖^2 ≤ ε + (π.prod π).real (replicaOverlapEvent ε) := by
  rw [norm_mean_spin_sq_eq_replica_overlap hN π hπ]
  have hE := replicaOverlapEvent_measurable (N := N) ε
  have hi : Integrable ((replicaOverlapEvent ε).indicator (fun _ => (1 : ℝ))) (π.prod π) :=
    (integrable_const _).indicator hE
  have hm := integral_mono_ae (sphereMeasure_overlap_integrable hN π hπ)
    ((integrable_const ε).add hi) (by
      filter_upwards [sphereMeasure_prod_support π hπ] with z hz
      have hR := (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2).2
      change overlap z.1 z.2 ≤ ε + (replicaOverlapEvent ε).indicator (fun _ => (1 : ℝ)) z
      by_cases he : z ∈ replicaOverlapEvent ε
      · rw [indicator_of_mem he]
        linarith
      · rw [indicator_of_notMem he, add_zero]
        change ¬ε < overlap z.1 z.2 at he
        exact le_of_not_gt he)
  change (∫ z, overlap z.1 z.2 ∂π.prod π) ≤
    ∫ z, ε + (replicaOverlapEvent ε).indicator (fun _ => (1 : ℝ)) z ∂π.prod π at hm
  rw [integral_add (integrable_const ε) hi, integral_const,
    probReal_univ, one_smul, integral_indicator_const _ hE, smul_eq_mul, mul_one] at hm
  exact hm

theorem norm_mean_spin_le (hN : 1 ≤ N)
    (π : Measure (Vector N)) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ x ∂π, ‖x‖^2 = (N : ℝ)) {ε : ℝ} (hε : 0 ≤ ε) :
    ‖∫ x, spin x ∂π‖ ≤ Real.sqrt ε + Real.sqrt ((π.prod π).real (replicaOverlapEvent ε)) := by
  have hb := norm_mean_spin_sq_le hN π hπ hε
  have hmass := measureReal_nonneg (μ := π.prod π) (s := replicaOverlapEvent ε)
  nlinarith [Real.sq_sqrt hε, Real.sq_sqrt hmass, Real.sqrt_nonneg ε,
    Real.sqrt_nonneg ((π.prod π).real (replicaOverlapEvent ε)), norm_nonneg (∫ x, spin x ∂π),
    mul_nonneg (Real.sqrt_nonneg ε) (Real.sqrt_nonneg ((π.prod π).real (replicaOverlapEvent ε)))]

/-- The source exponentially small replica mass supplies the actual
magnetization error with the exact half-rate exponential. -/
theorem mixture_magnetization_le_of_replica (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) {ε r : ℝ} (hε : 0 ≤ ε)
    (hrep : ((mixtureGibbsLaw μ β J).prod (mixtureGibbsLaw μ β J)).real (replicaOverlapEvent ε) ≤
      Real.exp (-r * N)) :
    ‖mean μ J β spin‖ ≤ Real.sqrt ε + Real.exp (-(r / 2) * N) := by
  let _ := mixtureGibbsLaw_probability hN μ β J
  have hs : ∀ᵐ x ∂mixtureGibbsLaw μ β J, ‖x‖^2 = (N : ℝ) :=
    gibbsLaw_support hN β (fieldOfMixture μ J)
  have hmean := norm_mean_spin_le hN (mixtureGibbsLaw μ β J) hs hε
  have hexp : Real.sqrt (Real.exp (-r * N)) = Real.exp (-(r / 2) * N) := by
    have he : (Real.exp (-(r / 2) * N))^2 = Real.exp (-r * N) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hs := Real.sqrt_sq (Real.exp_pos (-(r / 2) * N)).le
    rw [he] at hs
    exact hs
  exact hmean.trans (add_le_add le_rfl ((Real.sqrt_le_sqrt hrep).trans_eq hexp))

end SlowEquilibration.SphericalReplicaMagnetization
