-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.SphericalTaylorCoreLower
public import SlowEquilibration.SphereSupportedIntegrals

@[expose] public section

/-! # Literal source weighted partition and core/cap comparison

The actual source penalty gives a core lower bound and a two-region upper
bound. The low-overlap region has its exact constant source suppression;
the remaining region is bounded by the genuine cap partition.
-/
namespace SlowEquilibration.SphericalSourceWeightedPartition
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

/-- The source weighted partition against the actual uniform sphere law. -/
def sourceWeightedPartition (β : ℝ) (H : Vector N → ℝ)
    (J δ q₁ q₂ : ℝ) (x : Vector N) : ℝ :=
  ∫ u, Real.exp (β*H u-2*(N : ℝ)*sourceProfile J δ q₁ q₂ (overlap u x)) ∂sphereLaw N

theorem sourceWeightedPartition_integrable (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (J δ q₁ q₂ : ℝ) (x : Vector N) :
    Integrable (fun u => Real.exp (β*H u-2*(N : ℝ)*
      sourceProfile J δ q₁ q₂ (overlap u x))) (sphereLaw N) := by
  apply integrable_sphereSupported_continuous (sphereLaw N) (sphereLaw_support hN)
  have hR : Continuous (fun u : Vector N => overlap u x) := by unfold overlap; fun_prop
  exact Real.continuous_exp.comp ((hH.const_mul β).sub
    (((sourceProfile_contDiff J δ q₁ q₂).continuous.comp hR).const_mul (2*(N : ℝ))))

theorem sourceWeightedPartition_pos (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (J δ q₁ q₂ : ℝ) (x : Vector N) :
    0 < sourceWeightedPartition β H J δ q₁ q₂ x :=
  integral_exp_pos (sourceWeightedPartition_integrable hN β hH J δ q₁ q₂ x)

/-- The exact core partition is retained without penalty when the whole
core band lies above the second source cutoff. -/
theorem core_partition_le_sourceWeightedPartition (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (J δ q₁ q₂ q w : ℝ)
    (hq : q₁ < q₂) (hcore : q₂ ≤ q-w) (x : Vector N) :
    partitionOn β H (coreBand x q w) ≤ sourceWeightedPartition β H J δ q₁ q₂ x := by
  have hB := coreBand_measurable x q w
  have hi := integral_mono ((partition_integrand_integrable hN β hH).indicator hB)
    (sourceWeightedPartition_integrable hN β hH J δ q₁ q₂ x) (fun u => ?_)
  · rw [integral_indicator hB] at hi
    exact hi
  · by_cases hu : u ∈ coreBand x q w
    · rw [indicator_of_mem hu]
      have hR : q₂ ≤ overlap u x := by
        change |overlap u x-q| ≤ w at hu
        have hh := (abs_le.mp hu).1
        linarith
      have hz : sourceProfile J δ q₁ q₂ (overlap u x)=0 := profile_high _ hq hR
      rw [hz,mul_zero,sub_zero]
    · rw [indicator_of_notMem hu]
      exact (Real.exp_pos _).le

/-- Exact two-region upper bound; its primitive probabilities concern
only the full planted partition and a genuine positive cap partition. -/
theorem sourceWeightedPartition_le_suppressed_full_add_cap (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (J δ q₁ q₂ : ℝ)
    (hK : 0 ≤ sourceK J δ) (hq : q₁ < q₂) (x : Vector N) :
    sourceWeightedPartition β H J δ q₁ q₂ x ≤
      Real.exp (-2*(N : ℝ)*sourceK J δ)*partition N β H+partitionOn β H (cap x q₁) := by
  let a := Real.exp (-2*(N : ℝ)*sourceK J δ)
  have hiH := partition_integrand_integrable hN β hH
  have hiCap := hiH.indicator (cap_measurable x q₁)
  have hu : ∀ u : Vector N, Real.exp (β*H u-2*(N : ℝ)*
      sourceProfile J δ q₁ q₂ (overlap u x)) ≤
      a*Real.exp (β*H u)+(cap x q₁).indicator (fun u => Real.exp (β*H u)) u := by
    intro u
    by_cases hcap : u ∈ cap x q₁
    · rw [indicator_of_mem hcap]
      have hn : 0 ≤ sourceProfile J δ q₁ q₂ (overlap u x) := profile_nonneg _ _ _ hK _
      have hb : Real.exp (β*H u-2*(N : ℝ)*sourceProfile J δ q₁ q₂ (overlap u x)) ≤
          Real.exp (β*H u) := Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N])
      exact hb.trans (le_add_of_nonneg_left (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le))
    · rw [indicator_of_notMem hcap,add_zero]
      have hR : overlap u x ≤ q₁ := le_of_not_ge hcap
      have hz : sourceProfile J δ q₁ q₂ (overlap u x)=sourceK J δ := profile_low _ hq hR
      rw [hz,show β*H u-2*(N : ℝ)*sourceK J δ=
        -2*(N : ℝ)*sourceK J δ+β*H u by ring,Real.exp_add]
  have hb := integral_mono (sourceWeightedPartition_integrable hN β hH J δ q₁ q₂ x)
    ((hiH.const_mul a).add hiCap) hu
  change (∫ u, Real.exp (β*H u-2*(N : ℝ)*sourceProfile J δ q₁ q₂ (overlap u x))
    ∂sphereLaw N) ≤ (∫ u, a*Real.exp (β*H u)+
      (cap x q₁).indicator (fun u => Real.exp (β*H u)) u ∂sphereLaw N) at hb
  rw [integral_add (hiH.const_mul a) hiCap,integral_const_mul,
    integral_indicator (cap_measurable x q₁)] at hb
  exact hb

end
end SlowEquilibration.SphericalSourceWeightedPartition
