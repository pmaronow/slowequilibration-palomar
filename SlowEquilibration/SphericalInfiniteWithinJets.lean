-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureJetConcentration
public import SlowEquilibration.SphericalSeriesRegularity

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped BigOperators Topology ENNReal
open SphericalModel PureTensorJetBounds SphericalSeriesRegularity
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev physicalBallSet (N : ℕ) := closedBall (0 : Vector N) (Real.sqrt N)

def firstJetSeries {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) (x : Vector N) : Vector N →L[ℝ] ℝ :=
  ∑' p,fderiv ℝ (block μ p J) x

def secondJetSeries {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) (x : Vector N) :
    Vector N →L[ℝ] (Vector N →L[ℝ] ℝ) := ∑' p,fderiv ℝ (fderiv ℝ (block μ p J)) x

private theorem norm_tsum_bound {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (v : ℕ → E) (b : ℕ → ℝ) (hb : Summable b) (h : ∀ p,‖v p‖ ≤ b p) :
    ‖∑' p,v p‖ ≤ ∑' p,b p := by
  have hs : Summable (fun p => ‖v p‖) := hb.of_nonneg_of_le (fun p => norm_nonneg (v p)) h
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum h hb)

private theorem physicalBall_uniqueDiff {N : ℕ} (hN : 0 < N) : UniqueDiffOn ℝ (physicalBallSet N) := by
  apply uniqueDiffOn_convex (convex_closedBall _ _) 
  exact ⟨0,(isOpen_ball.subset_interior_iff.mpr ball_subset_closedBall) (mem_ball_self (by positivity))⟩

private theorem block_fderiv_bound {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (p : ℕ) (x : Vector N) (hx : x ∈ physicalBallSet N) :
    ‖fderiv ℝ (block μ p J) x‖ ≤ blockJetEnvelope μ 1 p J := by
  simpa only [norm_iteratedFDeriv_one] using block_iteratedFDeriv_norm_le hN μ 1 p J x
    (by simpa only [mem_closedBall,dist_zero_right] using hx)

private theorem block_second_fderiv_bound {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (p : ℕ) (x : Vector N) (hx : x ∈ physicalBallSet N) :
    ‖fderiv ℝ (fderiv ℝ (block μ p J)) x‖ ≤ blockJetEnvelope μ 2 p J := by
  rw [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact block_iteratedFDeriv_norm_le hN μ 2 p J x
    (by simpa only [mem_closedBall,dist_zero_right] using hx)

/-- The actual literal field has the summed ambient derivative on the entire
closed physical ball, including its boundary. -/
theorem field_hasFDerivWithinAt {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    HasFDerivWithinAt (field μ J) (firstJetSeries μ J x) (physicalBallSet N) x := by
  apply hasFDerivWithinAt_tsum_closedBall (fun p => block μ p J)
    (fun p => (block_contDiff μ p J).of_le (by simp)) 0 (by positivity)
    (fun p => blockJetEnvelope μ 0 p J) (fun p => blockJetEnvelope μ 1 p J)
    (hJ 0 (by omega)) (hJ 1 (by omega)) ?_ ?_ x hx
  · intro p y hy
    simpa only [norm_iteratedFDeriv_zero] using block_iteratedFDeriv_norm_le hN μ 0 p J y
      (by simpa only [mem_closedBall,dist_zero_right] using hy)
  · exact block_fderiv_bound hN μ J

theorem field_fderivWithin_eq {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    fderivWithin ℝ (field μ J) (physicalBallSet N) x = firstJetSeries μ J x :=
  (field_hasFDerivWithinAt hN μ J hJ x hx).fderivWithin (physicalBall_uniqueDiff hN x hx)

theorem firstJetSeries_hasFDerivWithinAt {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    HasFDerivWithinAt (firstJetSeries μ J) (secondJetSeries μ J x) (physicalBallSet N) x := by
  apply hasFDerivWithinAt_tsum_closedBall (fun p => fderiv ℝ (block μ p J))
    (fun p => (block_contDiff μ p J).fderiv_right (by simp)) 0 (by positivity)
    (fun p => blockJetEnvelope μ 1 p J) (fun p => blockJetEnvelope μ 2 p J)
    (hJ 1 (by omega)) (hJ 2 (by omega)) (block_fderiv_bound hN μ J)
    (block_second_fderiv_bound hN μ J) x hx

/-- The literal second derivative within the closed ball equals the genuine
uniformly convergent second ambient derivative series. -/
theorem field_second_fderivWithin_eq {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    fderivWithin ℝ (fun y => fderivWithin ℝ (field μ J) (physicalBallSet N) y) (physicalBallSet N) x =
      secondJetSeries μ J x := by
  rw [fderivWithin_congr' (fun y hy => field_fderivWithin_eq hN μ J hJ y hy) hx]
  exact (firstJetSeries_hasFDerivWithinAt hN μ J hJ x hx).fderivWithin (physicalBall_uniqueDiff hN x hx)

theorem field_fderivWithin_norm_le {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    ‖fderivWithin ℝ (field μ J) (physicalBallSet N) x‖ ≤ fullJetEnvelope μ 1 J := by
  rw [field_fderivWithin_eq hN μ J hJ x hx]
  have hb := fun p => block_fderiv_bound hN μ J p x hx
  have hs : Summable (fun p => ‖fderiv ℝ (block μ p J) x‖) :=
    (hJ 1 (by omega)).of_nonneg_of_le (fun p => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb (hJ 1 (by omega)))

theorem field_second_fderivWithin_norm_le {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : Vector N) (hx : x ∈ physicalBallSet N) :
    ‖fderivWithin ℝ (fun y => fderivWithin ℝ (field μ J) (physicalBallSet N) y) (physicalBallSet N) x‖ ≤
      fullJetEnvelope μ 2 J := by
  rw [field_second_fderivWithin_eq hN μ J hJ x hx]
  exact norm_tsum_bound (E := Vector N →L[ℝ] (Vector N →L[ℝ] ℝ))
    (fun p => fderiv ℝ (fderiv ℝ (block μ p J)) x) (fun p => blockJetEnvelope μ 2 p J)
    (hJ 2 (by omega)) (fun p => block_second_fderiv_bound hN μ J p x hx)


/-- The source three-jet event, interpreted as literal derivatives on the
closed physical ball, follows from the proved infinite Gaussian concentration. -/
theorem exists_uniform_withinJet_constants (μ : InfiniteMixture) :
    ∃ K c : ℝ,0 < K ∧ 0 < c ∧ ∀ N : ℕ,0 < N →
      disorderLaw N {J | ¬∀ x ∈ physicalBallSet N,
        ‖field μ J x‖ ≤ K*N ∧
        ‖fderivWithin ℝ (field μ J) (physicalBallSet N) x‖ ≤ K*Real.sqrt N ∧
        ‖fderivWithin ℝ (fun y => fderivWithin ℝ (field μ J) (physicalBallSet N) y)
          (physicalBallSet N) x‖ ≤ K} ≤ ENNReal.ofReal (4*Real.exp (-c*N)) := by
  obtain ⟨K,c,hK,hc,he⟩ := exists_threeJetEnvelope_constants μ
  refine ⟨K,c,hK,hc,fun N hN => (measure_mono_ae ?_).trans (he N hN)⟩
  filter_upwards [summableJetDisorder_ae hN μ] with J hJ
  intro hbad
  by_contra hgood
  have hg : ∀ j : Fin 3,fullJetEnvelope μ j.val J ≤ K*jetScale N j.val := by
    simpa only [mem_setOf_eq,not_exists,not_lt] using hgood
  apply hbad
  intro x hx
  have hg0 := hg 0
  have hg1 := hg 1
  have hg2 := hg ⟨2,by decide⟩
  simp only [Fin.val_zero,jetScale_zero] at hg0
  simp only [Fin.val_one,jetScale_one] at hg1
  simp only [jetScale_two,mul_one] at hg2
  exact ⟨(field_norm_le_fullJetEnvelope hN μ J hJ x
    (by simpa only [mem_closedBall,dist_zero_right] using hx)).trans hg0,
    (field_fderivWithin_norm_le hN μ J hJ x hx).trans hg1,
    (field_second_fderivWithin_norm_le hN μ J hJ x hx).trans hg2⟩

end SlowEquilibration.SphericalInfiniteModel
