-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalGroundLimit
public import SlowEquilibration.SphericalFiniteCritical

/-! Source 11.14's ordinary point-set count. The set cardinality equals
the original Kac--Rice score-window count almost surely, and its first
moment is uniformly bounded in each fixed centered window. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open LatitudeGroundTrial TwoAtomStationarity SphericalPairChartKacRice SphericalForm SphericalMorse
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

def sourceCriticalPhysicalWindowSet (n : ℕ) (μ : FiniteMixture) (Q l r : ℝ)
    (U : Set ℝ) (J : Disorder (n+3) μ.maxDegree) : Set (Vector (n+3)) :=
  {u | ‖u‖^2=(n+3:ℕ) ∧
    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
    field (centerCoefficients (mixtureCoefficients μ) Q) J u ∈ Icc l r ∧
    actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U}

def sourceCriticalPhysicalWindowCardMean (n : ℕ) (μ : FiniteMixture) (Q l r : ℝ)
    (U : Set ℝ) : ℝ :=
  (∫⁻ J, ((sourceCriticalPhysicalWindowSet n μ Q l r U J).ncard : ℝ≥0∞)
    ∂disorderLaw (n+3) μ.maxDegree).toReal

theorem source_score_window_count_eq_ordinary_card_of_finite
    (n : ℕ) (μ : FiniteMixture) (Q l r : ℝ) (U : Set ℝ)
    (J : Disorder (n+3) μ.maxDegree)
    (hfin : (sphereCriticalSet (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) J).Finite) :
    actualScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc l r) U) (fun _ _ => 1) J =
      ((sourceCriticalPhysicalWindowSet n μ Q l r U J).ncard : ℝ≥0∞) := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A := sourceCriticalPhysicalWindowSet n μ Q l r U J
  have hA : A.Finite := by
    apply hfin.subset
    intro u hu
    exact ⟨hu.1,hu.2.1⟩
  haveI : Fintype A := hA.fintype
  have hwindow : A = {u : Vector (n+3) | ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧
      actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U} := by
    ext u
    change (‖u‖^2=(n+3:ℕ) ∧ surfaceGradient (field c J) u=0 ∧
      field c J u ∈ Icc l r ∧ actualScore c J u 1 ∈ U) ↔
      (‖u‖^2=(n+3:ℕ) ∧ surfaceGradient (field c J) u=0 ∧
        actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U)
    rw [actualScore_mem_physicalEnergyWindow (by omega) c J u (Icc l r) U]
  unfold actualScoreWindowCount
  change (∑' u : {u : Vector (n+3) | ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧
      actualScore c J u ∈ physicalEnergyWindow (n+3) (Icc l r) U},
      (1:ℝ≥0∞)) = (A.ncard:ℝ≥0∞)
  rw [←hwindow]
  rw [tsum_fintype,Set.ncard_eq_toFinset_card A hA]
  simp

theorem sourceCriticalPhysicalWindowCardMean_eq_sourceCriticalWindowMean
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (l r : ℝ) (U : Set ℝ) :
    sourceCriticalPhysicalWindowCardMean n μ Q l r U =
      sourceCriticalWindowMean (n+1) μ Q U l r := by
  unfold sourceCriticalPhysicalWindowCardMean sourceCriticalWindowMean
  rw [sourceCriticalWindowMass_def]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [actual_sphere_criticalSet_finite_ae (n+2) (by omega) μ hQ]
    with J hfin
  exact (source_score_window_count_eq_ordinary_card_of_finite n μ Q l r U J hfin).symm

/-- Full mixed-model source 11.14: each fixed centered ordinary critical
set has a uniformly bounded expected cardinality, and the probability of
finding a point while the original maximum stays below the upper edge
has the printed iterated limit one. The same radial window and center are
used in both conclusions. -/
theorem source_mixed_actual_canonical_critical_counts_and_ground
    (μ : FiniteMixture) {β x Q δMax : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) (hδMax : 0 < δMax) :
    ∃ L R : ℝ, L < markK μ β Q ∧ markK μ β Q < R ∧
      sourceRadialEdge μ Q < L ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        (∀ t : ℝ, 0 < t →
          ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
            sourceCriticalPhysicalWindowCardMean n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) ≤ B) ∧
        Tendsto (fun t : ℝ => Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | (sourceCriticalPhysicalWindowSet n μ Q
              (d.center (n+1)-t) (d.center (n+1)+t) (Ioo L R) J).Nonempty ∧
              sourceSphereMaximum (n+1) μ Q J < d.center (n+1)+t}) atTop)
          atTop (𝓝 1) := by
  obtain ⟨L,R,hL,hR,hEdge,d,hLimit⟩ :=
    source_mixed_actual_canonical_joint_ground_iterated_limit μ h hnp hd hδMax
  refine ⟨L,R,hL,hR,hEdge,d,?_,?_⟩
  · intro t ht
    obtain ⟨B,hB,hbound⟩ := d.uniform_window_bound (-t) t (by linarith)
    refine ⟨B,hB,?_⟩
    intro n
    rw [sourceCriticalPhysicalWindowCardMean_eq_sourceCriticalWindowMean
      n μ h.overlap_range.1]
    simpa only [sub_eq_add_neg] using (hbound (n+1)).2
  · simpa only [sourceCriticalPhysicalWindowSet] using hLimit

end
end SlowEquilibration.PairConditionalDeterminantMoments
