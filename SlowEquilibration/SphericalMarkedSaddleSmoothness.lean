-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.RadialSaddleInverse
public import SlowEquilibration.SphericalMarkedSaddleCoefficients
public import SlowEquilibration.SphericalMaximumAllConclusions

/-! Smoothness of the genuine global radial maximizer on its exterior
energy domain, and on every original source-admissible nearby-energy band. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity
open scoped Topology ContDiff
set_option maxHeartbeats 400000

def sourceExteriorEnergyDomain (μ : FiniteMixture) (Q : ℝ) : Set ℝ :=
  {e | 2*sourceSaddleParameter μ Q*Real.sqrt (Q^2*μ.xi2 Q) < sourceSaddleEnergyCoefficient μ Q*e}

def sourceExteriorSaddle (μ : FiniteMixture) (Q e : ℝ) : ℝ :=
  RadialSaddleInverse.inverse (Q^2*μ.xi2 Q) (sourceSaddleParameter μ Q)
    (sourceSaddleEnergyCoefficient μ Q*e)

theorem sourceRadialProfile_concave (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) : ConcaveOn ℝ univ (sourceRadialProfile μ Q e) := by
  let κ := sourceMarkedLeastCurvature μ Q
  have hκ : 0 < κ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree;omega) hnp
  let embed : ℝ →ᵃ[ℝ] (ℝ × ℝ) := (AffineMap.const ℝ ℝ e).prod (AffineMap.id ℝ ℝ)
  have hSlice : ConcaveOn ℝ univ (fun k : ℝ => sourceRadialProfile μ Q e k+κ/2*(e^2+k^2)) := by
    simpa [embed,Function.comp_def] using
      (sourceMarkedComplexity_strongly_concave μ h.overlap_range.1 hnp).comp_affineMap embed
  have hCorrection : ConvexOn ℝ univ (fun k : ℝ => κ/2*(e^2+k^2)) := by
    have hSq := (Even.convexOn_pow (show Even (2 : ℕ) by decide)).smul (show 0 ≤ κ/2 by positivity)
    apply (hSq.add_const (κ/2*e^2)).congr
    intro k _
    simp only [Pi.add_apply,smul_eq_mul]
    ring
  apply (hSlice.sub hCorrection).congr
  intro k _
  change sourceRadialProfile μ Q e k+κ/2*(e^2+k^2)-κ/2*(e^2+k^2)=sourceRadialProfile μ Q e k
  ring

theorem sourceExteriorSaddle_facts (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (e : ℝ) (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    2*Real.sqrt (Q^2*μ.xi2 Q) < sourceExteriorSaddle μ Q e ∧
      sourceSaddleParameter μ Q*sourceExteriorSaddle μ Q e+
        Real.sqrt ((sourceExteriorSaddle μ Q e)^2-4*(Q^2*μ.xi2 Q))=sourceSaddleEnergyCoefficient μ Q*e :=
  RadialSaddleInverse.inverse_facts (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))
    (sourceSaddleParameter_gt_one μ hQ hnp) he

theorem sourceExteriorSaddle_stationary (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (e : ℝ) (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    sourceRadialProfileDerivative μ Q e (sourceExteriorSaddle μ Q e)=0 := by
  obtain ⟨hEdge,hEq⟩ := sourceExteriorSaddle_facts μ hQ hnp e he
  rw [sourceRadialProfileDerivative_root_eq μ hQ e _ hEdge]
  rw [show sourceSaddleEnergyCoefficient μ Q*e-sourceSaddleParameter μ Q*sourceExteriorSaddle μ Q e-
    Real.sqrt ((sourceExteriorSaddle μ Q e)^2-4*(Q^2*μ.xi2 Q))=0 by linarith,zero_div]

/-- The smooth explicit root equals the genuine unique global maximizer.
The global maximum and stationarity are both derived from the actual model. -/
theorem sourceRadialSaddle_eq_exterior (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    sourceRadialSaddle μ Q e=sourceExteriorSaddle μ Q e := by
  apply (sourceRadialSaddle_eq_of_global_max μ h hnp e (sourceExteriorSaddle μ Q e) ?_).symm
  have hEdge := (sourceExteriorSaddle_facts μ h.overlap_range.1 hnp e he).1
  have hStat := sourceExteriorSaddle_stationary μ h.overlap_range.1 hnp e he
  have hDeriv : HasDerivAt (sourceRadialProfile μ Q e) 0 (sourceExteriorSaddle μ Q e) := by
    rw [←hStat]
    exact sourceRadialProfile_hasDerivAt μ h.overlap_range.1 e _ hEdge
  exact fun j => RadialQuadraticBounds.concave_max_of_stationary
    (sourceRadialProfile_concave μ h hnp e) (mem_univ _) hDeriv j (mem_univ _)

theorem sourceRadialSaddle_exteriorDomain_of_above_edge (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (e : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < sourceRadialSaddle μ Q e) :
    e ∈ sourceExteriorEnergyDomain μ Q := by
  have hStat := sourceRadialSaddle_stationary_of_above_edge μ h hnp e hk
  rw [sourceRadialProfileDerivative_root_eq μ h.overlap_range.1 e _ hk] at hStat
  have hb := mul_pos (sq_pos_of_pos h.overlap_range.1) (μ.xi2_pos h.overlap_range.1)
  have hd : 0 < sourceSaddleParameter μ Q := lt_trans (by norm_num) (sourceSaddleParameter_gt_one μ h.overlap_range.1 hnp)
  have hnum := (div_eq_zero_iff).mp hStat
  rcases hnum with hnum|hden
  · have hLower := mul_lt_mul_of_pos_left hk hd
    change 2*sourceSaddleParameter μ Q*Real.sqrt (Q^2*μ.xi2 Q) < sourceSaddleEnergyCoefficient μ Q*e
    nlinarith [Real.sqrt_nonneg ((sourceRadialSaddle μ Q e)^2-4*(Q^2*μ.xi2 Q))]
  · exfalso
    nlinarith

theorem sourceExteriorSaddle_contDiffOn (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    ContDiffOn ℝ ∞ (sourceExteriorSaddle μ Q) (sourceExteriorEnergyDomain μ Q) := by
  have hInv := RadialSaddleInverse.inverse_contDiffOn (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ))
    (sourceSaddleParameter_gt_one μ hQ hnp)
  exact hInv.comp (by fun_prop : ContDiffOn ℝ ∞ (fun e : ℝ => sourceSaddleEnergyCoefficient μ Q*e)
    (sourceExteriorEnergyDomain μ Q)) (fun _ he => he)

theorem sourceRadialSaddle_contDiffOn_exterior (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ContDiffOn ℝ ∞ (sourceRadialSaddle μ Q) (sourceExteriorEnergyDomain μ Q) := by
  apply (sourceExteriorSaddle_contDiffOn μ h.overlap_range.1 hnp).congr
  intro e he
  exact sourceRadialSaddle_eq_exterior μ h hnp e he

theorem sourceRadialSaddle_band_subset_exterior (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    Icc (markE μ β x Q-δ) (markE μ β x Q+δ) ⊆ sourceExteriorEnergyDomain μ Q := by
  intro e he
  apply sourceRadialSaddle_exteriorDomain_of_above_edge μ h hnp e
  have hu := sourceRadialClearance_pos μ hm
  have hDist := hA4 e he
  have hmem : sourceRadialSaddle μ Q e ∈ Ioo L R := by
    by_contra hout
    have hzero := Metric.infDist_le_dist_of_mem (x := sourceRadialSaddle μ Q e)
      (show sourceRadialSaddle μ Q e ∈ (Ioo L R)ᶜ from hout)
    rw [dist_self] at hzero
    nlinarith
  exact hL.trans hmem.1

/-- Source band smoothness uses the literal source A4 clearance of the
internally selected actual global radial saddle, rather than a smoothness input. -/
theorem sourceRadialSaddle_contDiffOn_band (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    ContDiffOn ℝ ∞ (sourceRadialSaddle μ Q) (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) :=
  (sourceRadialSaddle_contDiffOn_exterior μ h hnp).mono
    (sourceRadialSaddle_band_subset_exterior μ h hnp hL hm hA4)

end SlowEquilibration.SphericalMarkedWindows
