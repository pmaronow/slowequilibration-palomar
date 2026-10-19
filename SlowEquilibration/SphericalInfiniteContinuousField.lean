-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteJetSeries
public import Mathlib.Topology.ContinuousMap.Compact

/-! A genuine random continuous field on the closed physical ball, with a
simultaneous almost-everywhere identification with the original tensor series. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel PureTensorJetBounds
open scoped Topology RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev PhysicalBall (N : ℕ) := ↥(Metric.closedBall (0 : Vector N) (Real.sqrt N))
instance (N : ℕ) : CompactSpace (PhysicalBall N) :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : Vector N) (Real.sqrt N))

/-- The actual weighted finite tensor polynomial restricted to the physical ball. -/
def blockContinuous {N : ℕ} (μ : InfiniteMixture) (p : ℕ) (J : Disorder N) :
    C(PhysicalBall N,ℝ) :=
  ⟨fun x => block μ p J x, (block_contDiff μ p J).continuous.comp continuous_subtype_val⟩

theorem blockContinuous_norm_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (p : ℕ) (J : Disorder N) :
    ‖blockContinuous μ p J‖≤blockJetEnvelope μ 0 p J := by
  apply (ContinuousMap.norm_le _ (blockJetEnvelope_nonneg hN μ 0 p J)).2
  intro x
  simpa only [blockContinuous,ContinuousMap.coe_mk,norm_iteratedFDeriv_zero] using
    block_iteratedFDeriv_norm_le hN μ 0 p J x
      (by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property)

theorem blockContinuous_continuous {N : ℕ} (μ : InfiniteMixture) (p : ℕ) :
    Continuous (blockContinuous (N := N) μ p) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun a : Disorder N × PhysicalBall N => block μ p a.1 a.2)
  unfold block SphericalAging.FiniteModel.Hamiltonian SphericalAging.FiniteModel.tensorMonomial
  fun_prop

/-- This is always a continuous function. On the genuine probability-one
summability event it is the original pointwise field at every ball point. -/
def continuousField {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) : C(PhysicalBall N,ℝ) :=
  ∑' p,blockContinuous μ p J

theorem continuousField_measurable {N : ℕ} (μ : InfiniteMixture) :
    Measurable (continuousField (N := N) μ) :=
  Measurable.tsum (fun p => (blockContinuous_continuous μ p).measurable)

theorem summable_blockContinuous_norm {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) :
    Summable (fun p => ‖blockContinuous μ p J‖) :=
  (hJ 0 (by omega)).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun p => blockContinuous_norm_le hN μ p J)

theorem continuousField_apply {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (x : PhysicalBall N) :
    continuousField μ J x=field μ J x := by
  exact (ContinuousMap.evalCLM ℝ x).map_tsum (summable_blockContinuous_norm hN μ J hJ).of_norm

theorem continuousField_eq_original_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) :
    ∀ᵐ J ∂disorderLaw N,∀ x : PhysicalBall N,continuousField μ J x=field μ J x := by
  filter_upwards [summableJetDisorder_ae hN μ] with J hJ
  exact continuousField_apply hN μ J hJ

theorem originalField_continuousOn_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) :
    ∀ᵐ J ∂disorderLaw N,ContinuousOn (field μ J)
      (Metric.closedBall (0 : Vector N) (Real.sqrt N)) := by
  filter_upwards [continuousField_eq_original_ae hN μ] with J hJ
  rw [continuousOn_iff_continuous_restrict]
  exact (continuousField μ J).continuous.congr hJ

end SlowEquilibration.SphericalInfiniteModel
