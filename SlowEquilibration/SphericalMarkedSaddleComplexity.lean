-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalMarkedSaddleSmoothness
public import SlowEquilibration.SphericalMarkedComplexitySmoothness

/-! The true optimized marked complexity on the actual radial saddle,
including exterior smoothness, its envelope derivative and a global contact
quadratic remainder stronger than the source nearby-energy Taylor estimate. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set TwoAtomStationarity SphericalSequentialRegression
open scoped Topology ContDiff
set_option maxHeartbeats 400000

def sourceSaddleComplexity (μ : FiniteMixture) (Q e : ℝ) : ℝ :=
  sourceRadialProfile μ Q e (sourceRadialSaddle μ Q e)

theorem sourceExteriorEnergyDomain_isOpen (μ : FiniteMixture) (Q : ℝ) :
    IsOpen (sourceExteriorEnergyDomain μ Q) :=
  isOpen_lt continuous_const (continuous_const.mul continuous_id)

theorem sourceRadialSaddle_contDiffAt_exterior (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    {e : ℝ} (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    ContDiffAt ℝ ∞ (sourceRadialSaddle μ Q) e :=
  (sourceRadialSaddle_contDiffOn_exterior μ h hnp).contDiffAt
    ((sourceExteriorEnergyDomain_isOpen μ Q).mem_nhds he)

theorem sourceSaddleComplexity_contDiffAt_exterior (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    {e : ℝ} (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    ContDiffAt ℝ ∞ (sourceSaddleComplexity μ Q) e := by
  have hEdge := (sourceExteriorSaddle_facts μ h.overlap_range.1 hnp e he).1
  rw [←sourceRadialSaddle_eq_exterior μ h hnp e he] at hEdge
  have hSaddle := sourceRadialSaddle_contDiffAt_exterior μ h hnp he
  have hPair : ContDiffAt ℝ ∞ (fun v : ℝ => (v,sourceRadialSaddle μ Q v)) e :=
    contDiffAt_id.prodMk hSaddle
  have hComp : ContDiffAt ℝ ∞
      ((fun z : ℝ×ℝ => sourceRadialProfile μ Q z.1 z.2) ∘
        (fun v : ℝ => (v,sourceRadialSaddle μ Q v))) e :=
    (sourceMarkedComplexity_contDiffAt μ h.overlap_range.1 e _ hEdge).comp e hPair
  exact hComp

/-- The envelope derivative is the literal actual energy score at the true
global radial saddle. Stationarity and saddle smoothness are proved internally. -/
theorem sourceSaddleComplexity_hasDerivAt (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    {e : ℝ} (he : e ∈ sourceExteriorEnergyDomain μ Q) :
    HasDerivAt (sourceSaddleComplexity μ Q) (-sourceEnergySlope μ Q e (sourceRadialSaddle μ Q e)) e := by
  have hEdge := (sourceExteriorSaddle_facts μ h.overlap_range.1 hnp e he).1
  rw [←sourceRadialSaddle_eq_exterior μ h hnp e he] at hEdge
  have hSaddle := sourceRadialSaddle_contDiffAt_exterior μ h hnp he
  have hCurve : HasDerivAt (fun v : ℝ => (v,sourceRadialSaddle μ Q v))
      (1,deriv (sourceRadialSaddle μ Q) e) e :=
    (hasDerivAt_id e).prodMk (hSaddle.differentiableAt (by simp)).hasDerivAt
  have hComp : HasDerivAt
      ((fun z : ℝ×ℝ => sourceRadialProfile μ Q z.1 z.2) ∘
        (fun v : ℝ => (v,sourceRadialSaddle μ Q v)))
      (sourceMarkedGradient μ Q e (sourceRadialSaddle μ Q e)
        (1,deriv (sourceRadialSaddle μ Q) e)) e :=
    (sourceMarkedComplexity_hasFDerivAt μ h.overlap_range.1 e _ hEdge).comp_hasDerivAt e hCurve
  have hStat := sourceRadialSaddle_stationary_of_above_edge μ h hnp e hEdge
  change HasDerivAt (sourceSaddleComplexity μ Q)
    (sourceMarkedGradient μ Q e (sourceRadialSaddle μ Q e) (1,deriv (sourceRadialSaddle μ Q) e)) e at hComp
  have hGradient : sourceMarkedGradient μ Q e (sourceRadialSaddle μ Q e)
      (1,deriv (sourceRadialSaddle μ Q) e)=-sourceEnergySlope μ Q e (sourceRadialSaddle μ Q e) := by
    simp [sourceMarkedGradient,hStat]
  rw [hGradient] at hComp
  exact hComp

theorem sourceContact_energy_in_exterior_domain (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    markE μ β x Q ∈ sourceExteriorEnergyDomain μ Q := by
  apply sourceRadialSaddle_exteriorDomain_of_above_edge μ h hnp
  rw [sourceRadialSaddle_at_contact μ h hnp]
  exact sourceContact_markK_above_edge μ h

theorem sourceSaddleComplexity_at_contact (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    sourceSaddleComplexity μ Q (markE μ β x Q)=0 := by
  unfold sourceSaddleComplexity
  rw [sourceRadialSaddle_at_contact μ h hnp,sourceContact_radialProfile_zero μ h hnp]

theorem sourceSaddleComplexity_contact_hasDerivAt (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    HasDerivAt (sourceSaddleComplexity μ Q) (-(β*x)) (markE μ β x Q) := by
  have hd := sourceSaddleComplexity_hasDerivAt μ h hnp (sourceContact_energy_in_exterior_domain μ h hnp)
  rw [sourceRadialSaddle_at_contact μ h hnp,sourceEnergySlope_at_contact μ h hnp] at hd
  exact hd

theorem sourceSaddleComplexity_contDiffOn_band (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA4 : ∀ e ∈ Icc (markE μ β x Q-δ) (markE μ β x Q+δ),
      sourceRadialClearance μ β Q (Ioo L R)/2 ≤ Metric.infDist (sourceRadialSaddle μ Q e) (Ioo L R)ᶜ) :
    ContDiffOn ℝ ∞ (sourceSaddleComplexity μ Q) (Icc (markE μ β x Q-δ) (markE μ β x Q+δ)) := by
  intro e he
  exact (sourceSaddleComplexity_contDiffAt_exterior μ h hnp
    (sourceRadialSaddle_band_subset_exterior μ h hnp hL hm hA4 he)).contDiffWithinAt

theorem sourceContact_fixed_radial_energy_expansion (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (e : ℝ) :
    sourceRadialProfile μ Q e (markK μ β Q)=
      -(β*x)*(e-markE μ β x Q)-sourceEnergyCurvature μ Q/2*(e-markE μ β x Q)^2 := by
  have hq := source_scoreQuadratic_joint_expansion μ Q (markE μ β x Q) (markK μ β Q) e (markK μ β Q)
  rw [sourceEnergySlope_at_contact μ h hnp] at hq
  simp only [sub_self,mul_zero,zero_pow (by norm_num : 2 ≠ 0),add_zero] at hq
  have hZero := sourceContact_radialProfile_zero μ h hnp
  change 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (markE μ β x Q,markK μ β Q))/2+
    SemicirclePotential.potential (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))=0 at hZero
  change 1/2+Real.log ((Q^2*μ.xi2 Q)/(Q*μ.xi1 Q))/2-
    scoreQuadratic μ Q (scorePairEquiv (e,markK μ β Q))/2+
    SemicirclePotential.potential (markK μ β Q/Real.sqrt (Q^2*μ.xi2 Q))=_
  rw [hq]
  nlinarith

/-- A global quantitative quadratic contact remainder for the actual
optimized complexity; this implies the printed nearby-energy O((e-E0)^2). -/
theorem sourceSaddleComplexity_contact_taylor (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) (e : ℝ) :
    |sourceSaddleComplexity μ Q e+(β*x)*(e-markE μ β x Q)| ≤
      sourceEnergyCurvature μ Q/2*(e-markE μ β x Q)^2 := by
  have hLower := sourceRadialSaddle_global_max μ h hnp e (markK μ β Q)
  rw [sourceContact_fixed_radial_energy_expansion μ h hnp e] at hLower
  have hUpper := sourceMarkedComplexity_global_loss μ h hnp e (sourceRadialSaddle μ Q e)
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1 (by have hd := h.min_degree;omega) hnp
  have hpen : 0 ≤ sourceMarkedLeastCurvature μ Q*((e-markE μ β x Q)^2+
      (sourceRadialSaddle μ Q e-markK μ β Q)^2)/2 := by positivity
  change -(β*x)*(e-markE μ β x Q)-sourceEnergyCurvature μ Q/2*(e-markE μ β x Q)^2 ≤
    sourceSaddleComplexity μ Q e at hLower
  change sourceSaddleComplexity μ Q e ≤ _ at hUpper
  have hnonpos : sourceSaddleComplexity μ Q e+(β*x)*(e-markE μ β x Q) ≤ 0 := by linarith
  rw [abs_of_nonpos hnonpos]
  linarith

end SlowEquilibration.SphericalMarkedWindows
