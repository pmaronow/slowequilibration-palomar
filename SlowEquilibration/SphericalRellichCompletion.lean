-- SPDX-License-Identifier: Apache-2.0
-- Adapted from openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
-- lean/OAI/Geometry/NodalSets/Charts/SphereEnergyL2Compact.lean.
-- Modifications: literal Gibbs smooth-gradient graph closure and its actual
-- continuous L² projection; Lean 4.35 public module syntax.
module

public import SlowEquilibration.SphericalWeakResolvent
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Sequences

@[expose] public section

namespace SlowEquilibration.SphericalForm

open MeasureTheory Filter Metric Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped Topology

/-- The smooth-core Rellich property used solely as an explicit hypothesis
of the closure-transfer infrastructure below. The actual chart proof supplies
this property separately. -/
def SmoothRellich {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H) : Prop :=
  ∀ (f : ℕ → smoothCore N) (C : ℝ), 0 < C →
    (∀ j, ‖smoothGradientGraphLinear hN β H hH (f j)‖ ≤ C) →
    ∃ ν : ℕ → ℕ, StrictMono ν ∧
      CauchySeq (fun j => (smoothGradientGraphLinear hN β H hH (f (ν j))).fst)

/-- Infrastructure: the proved smooth-core Rellich property transfers to
bounded sequences in the actual spherical Sobolev graph closure. -/
theorem sphericalEnergyL2Map_bounded_subsequence_of_smoothRellich {N : ℕ}
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (hRellich : SmoothRellich hN β H hH)
    (z : ℕ → sphericalSobolevGraph hN β H hH) {C : ℝ} (hC : 0 < C)
    (hb : ∀ j, ‖z j‖ ≤ C) :
    ∃ ν : ℕ → ℕ, StrictMono ν ∧ ∃ v : Lp ℝ 2 (gibbsLaw N β H),
      Tendsto (fun j => sphericalEnergyL2Map hN β H hH (z (ν j))) atTop (𝓝 v) := by
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  have hm (j : ℕ) : (z j).val ∈ closure (Set.range (smoothGradientGraphLinear hN β H hH)) :=
    (z j).property
  have ha (j : ℕ) := Metric.mem_closure_iff.mp (hm j) _ (he j)
  choose w hw hd using ha
  choose f hf using hw
  have hdist (j : ℕ) :
      dist (smoothGradientGraphLinear hN β H hH (f j)) (z j).val < 1/((j:ℝ)+1) := by
    rw [hf j, dist_comm]
    exact hd j
  have hbound (j : ℕ) : ‖smoothGradientGraphLinear hN β H hH (f j)‖ ≤ C+1 := by
    have hn := norm_le_norm_add_const_of_dist_le (hdist j).le
    have he1 : 1/((j:ℝ)+1) ≤ 1 := (div_le_one (by positivity)).mpr
      (by linarith [Nat.cast_nonneg (α := ℝ) j])
    have hz : ‖(z j).val‖ ≤ C := hb j
    linarith
  obtain ⟨ν, hν, hc⟩ := hRellich f (C+1) (by positivity) hbound
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨ν, hν, v, hv.congr_dist ?_⟩
  have he0 : Tendsto (fun j : ℕ => 1/((ν j:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hν.tendsto_atTop
  apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_) he0
  rw [dist_eq_norm]
  change ‖(smoothGradientGraphLinear hN β H hH (f (ν j)) - (z (ν j)).val).fst‖ ≤ _
  exact (WithLp.norm_fst_le _ _).trans
    (by simpa only [← dist_eq_norm] using (hdist (ν j)).le)

/-- Infrastructure: a genuine smooth-core Rellich theorem makes the actual
spherical graph inclusion a compact operator. This theorem does not assert
the smooth-core premise without its separate chart proof. -/
theorem sphericalEnergyL2Map_compact_of_smoothRellich {N : ℕ}
    (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    (hRellich : SmoothRellich hN β H hH) :
    IsCompactOperator (sphericalEnergyL2Map hN β H hH) := by
  apply (isCompactOperator_iff_isCompact_closure_image_closedBall
    (sphericalEnergyL2Map hN β H hH).toLinearMap zero_lt_one).mpr
  apply IsSeqCompact.isCompact
  intro y hy
  have he (j : ℕ) : 0 < 1/((j:ℝ)+1) := by positivity
  have ha (j : ℕ) := Metric.mem_closure_iff.mp (hy j) _ (he j)
  choose w hw hd using ha
  choose z hz hzw using hw
  have hb (j : ℕ) : ‖z j‖ ≤ (1:ℝ) := by
    simpa only [mem_closedBall, dist_zero_right] using hz j
  obtain ⟨ν, hν, v, hv⟩ :=
    sphericalEnergyL2Map_bounded_subsequence_of_smoothRellich hN β H hH hRellich z zero_lt_one hb
  have hconv : Tendsto (y ∘ ν) atTop (𝓝 v) := by
    apply hv.congr_dist
    apply squeeze_zero (fun j => dist_nonneg) (fun j => ?_)
      (tendsto_one_div_add_atTop_nhds_zero_nat.comp hν.tendsto_atTop)
    have hh := (hd (ν j)).le
    rw [← hzw (ν j)] at hh
    simpa only [Function.comp_apply, dist_comm] using! hh
  refine ⟨v, ?_, ν, hν, hconv⟩
  exact isClosed_closure.mem_of_tendsto hconv (Eventually.of_forall (fun j => hy (ν j)))

end SlowEquilibration.SphericalForm
