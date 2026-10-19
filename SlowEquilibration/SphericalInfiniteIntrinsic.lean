-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteJetSeries
public import SlowEquilibration.SphericalSeriesRegularity
public import SlowEquilibration.SphericalIntrinsicSpectral

/-! Genuine intrinsic regularity and the actual weighted spherical form and
spectrum for the source infinite tensor field. The random series is proved
regular on its actual probability-one event, rather than assuming regularity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel SphericalIntrinsicExtension
open SphericalSeriesRegularity
open scoped Topology
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal infinite field restricted to the manuscript round sphere. -/
def intrinsicField (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) : RoundSphere n → ℝ :=
  fun x => field μ J x

theorem field_contDiffOn_closedBall {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) :
    ContDiffOn ℝ 2 (field μ J) (Metric.closedBall (0 : Vector N) (Real.sqrt N)) := by
  apply contDiffOn_tsum_two_closedBall (fun p => block μ p J)
    (fun p => (block_contDiff μ p J).of_le le_top) (0 : Vector N)
    (Real.sqrt_pos.mpr (by exact_mod_cast hN))
    (fun j p => blockJetEnvelope μ j.val p J)
    (fun j => hJ j.val (by omega))
  intro j p x hx
  exact block_iteratedFDeriv_norm_le hN μ j.val p J x
    (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx)

theorem intrinsicField_contDiff (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (hJ : J∈summableJetDisorder μ) : IntrinsicContDiff n 2 (intrinsicField n μ J) := by
  exact intrinsicContDiff_tsum_two n (fun p => block μ p J)
    (fun p => (block_contDiff μ p J).of_le le_top)
    (fun j p => blockJetEnvelope μ j.val p J)
    (fun j => hJ j.val (by omega))
    (fun j p x hx => block_iteratedFDeriv_norm_le (by omega) μ j.val p J x hx)

theorem intrinsicField_contDiff_ae (n : ℕ) (μ : InfiniteMixture) :
    ∀ᵐ J ∂disorderLaw (n+1),IntrinsicContDiff n 2 (intrinsicField n μ J) := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  exact intrinsicField_contDiff n μ J hJ

/-- A globally C² representative, equal to the original infinite field on the
sphere almost surely. The exceptional null set is represented by the zero field. -/
def regularAmbientField (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) : Vector (n+1) → ℝ :=
  if J∈summableJetDisorder μ then ambientExtension n (intrinsicField n μ J) else 0

theorem regularAmbientField_contDiff (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) :
    ContDiff ℝ 2 (regularAmbientField n μ J) := by
  classical
  unfold regularAmbientField
  split_ifs with hJ
  · exact ambientExtension_contDiff n 2 _ (intrinsicField_contDiff n μ J hJ)
  · exact contDiff_const

theorem regularAmbientField_restrict_ae (n : ℕ) (μ : InfiniteMixture) :
    ∀ᵐ J ∂disorderLaw (n+1),∀ x : RoundSphere n,
      regularAmbientField n μ J x=field μ J x := by
  filter_upwards [summableJetDisorder_ae (by omega : 0<n+1) μ] with J hJ
  intro x
  rw [regularAmbientField,if_pos hJ,ambientExtension_restrict]
  rfl

/-- The actual normalized compact-L² spectrum of the genuine infinite field's
weighted spherical Dirichlet form. No spectral estimate is included as a premise. -/
def infiniteSpectralData (n : ℕ) (hn : 1≤n) (β : ℝ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) :=
  SphericalForm.normalizedSphericalSpectralData (show 2≤n+1 by omega) β
    (regularAmbientField n μ J) (regularAmbientField_contDiff n μ J).continuous

theorem infiniteSpectralData_eq_intrinsic (n : ℕ) (hn : 1≤n) (β : ℝ)
    (μ : InfiniteMixture) (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (k : ℕ) :
    (infiniteSpectralData n hn β μ J).eigenvalue k = (intrinsicSpectralData n hn β
      (intrinsicField n μ J) ((intrinsicField_contDiff n μ J hJ).of_le (by norm_num))).eigenvalue k := by
  let L : {H : Vector (n+1) → ℝ // Continuous H} → ℝ := fun H =>
    (SphericalForm.normalizedSphericalSpectralData (show 2≤n+1 by omega) β H.1 H.2).eigenvalue k
  change L ⟨regularAmbientField n μ J,(regularAmbientField_contDiff n μ J).continuous⟩=
    L ⟨ambientExtension n (intrinsicField n μ J),
      (ambientExtension_contDiff n 1 _ ((intrinsicField_contDiff n μ J hJ).of_le (by norm_num))).continuous⟩
  apply congrArg L
  apply Subtype.ext
  exact if_pos hJ

end SlowEquilibration.SphericalInfiniteModel
