-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeAllLatitudeUpper
public import SlowEquilibration.SphericalPlateauAmplitudePoleTail
public import SlowEquilibration.SphericalWeightedTrialBankConnector
public import SlowEquilibration.SphericalWeightedTrialLocalizationGap

@[expose] public section

/-! # Literal weighted amplitude partition and physical latitude profile

The actual weighted potential has a constant planted drift and source
penalty on every latitude law. Its coarea profile is therefore the actual
sampled Gaussian latitude pressure plus the literal drift, source penalty
and finite-dimensional spherical entropy coefficient.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter SphericalForm
open scoped Topology
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

def amplitudeSourcePotential (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (D : BankDisorder n μ) : Vector (n+1) → ℝ :=
  weightedPotential β (amplitudePlantedField μ β x (latitudeFrameAt x) p₀ s D)
    (sourceProfile J δ q₁ q₂) x

theorem amplitudeSourcePotential_continuous (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    Continuous (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D) :=
  weightedPotential_continuous β (amplitudePlantedField_contDiff μ β x (latitudeFrameAt x) p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂).continuous x

theorem amplitudePartition_eq_partition (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D=
      partition (n+1) 1 (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D) := by
  unfold amplitudePartition partition amplitudeSourcePotential weightedPotential
  simp only [one_mul,Nat.cast_add,Nat.cast_one]

theorem amplitudeRestrictedPartition_eq_partitionOn (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (E : Set (Vector (n+1))) (D : BankDisorder n μ) :
    amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D=
      partitionOn 1 (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D) E := by
  unfold amplitudeRestrictedPartition partitionOn amplitudeSourcePotential weightedPotential
  simp only [one_mul,Nat.cast_add,Nat.cast_one]

/-- Exact physical weighted mass is the literal restricted partition
divided by the literal full weighted amplitude partition. -/
theorem amplitudeWeightedLaw_real_eq_partition_ratio (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (E : Set (Vector (n+1))) (hE : MeasurableSet E) (D : BankDisorder n μ) :
    (amplitudeWeightedLaw μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D).real E=
      amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s E D/
        amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D := by
  unfold amplitudeWeightedLaw
  rw [weightedLaw_eq_gibbsLaw (by omega : 1 ≤ n+1) β
    (amplitudePlantedField_contDiff μ β x (latitudeFrameAt x) p₀ s D).continuous
    (sourceProfile_contDiff J δ q₁ q₂)]
  change (gibbsLaw (n+1) 1 (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D)).real E=_
  rw [gibbsLaw_real_eq_partitionOn_div (by omega : 1 ≤ n+1) 1
    (amplitudeSourcePotential_continuous μ β J δ q₁ q₂ x p₀ s D) hE]
  rw [amplitudeRestrictedPartition_eq_partitionOn,amplitudePartition_eq_partition]

theorem amplitudeLatitude_weighted_partition (hn : 1 ≤ n) (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r| ≤ 1) (D : BankDisorder n μ) :
    partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) 1
      (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D)=
      Real.exp (((n+1:ℕ):ℝ)*(β^2*μ.xi r-2*sourceProfile J δ q₁ q₂ r))*
        partitionAgainst (latitudeLaw x (latitudeFrameAt x) r) β
          (amplitudeField μ x (latitudeFrameAt x) p₀ s D) := by
  unfold partitionAgainst
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr] with u hu
  have hR : overlap x u=r := by
    rw [show overlap x u=overlap u x by unfold overlap;rw [real_inner_comm]]
    exact hu.2
  unfold amplitudeSourcePotential weightedPotential amplitudePlantedField
  rw [hR,← Real.exp_add]
  congr 1
  simp only [one_mul,Nat.cast_add,Nat.cast_one]
  ring

theorem amplitudeLatitude_weighted_profile (hn : 1 ≤ n) (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1:ℕ):ℝ)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) {r : ℝ} (hr : |r| ≤ 1) (D : BankDisorder n μ) :
    latitudePartitionProfile n 1 (amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D) x r=
      amplitudeLatitudeSampledPressure μ β x p₀ s r D+β^2*μ.xi r-
        2*sourceProfile J δ q₁ q₂ r+
        ((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ))*Real.log (1-r^2) := by
  have hs := (latitudeLaw_support hn x hx (latitudeFrameAt x) (latitudeFrameAt_orthogonal x hx) hr).mono fun _ hu => hu.1
  have hZ := partitionAgainst_pos _ hs β (amplitudeField_contDiff μ x (latitudeFrameAt x) p₀ s D).continuous
  unfold latitudePartitionProfile amplitudeLatitudeSampledPressure amplitudeLatitudeLogPartition
  rw [amplitudeLatitude_weighted_partition hn μ β J δ q₁ q₂ x hx p₀ s hr D,
    Real.log_mul (Real.exp_pos _).ne' hZ.ne',Real.log_exp]
  have hN : ((n+1:ℕ):ℝ)≠0 := by positivity
  field_simp
  ring

theorem amplitudeEntropyCorrection_le (hn : 2 ≤ n) {ρ r : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hr : |r| ≤ ρ) :
    ((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ))*Real.log (1-r^2) ≤ Real.log (1-r^2)/2+(-3*Real.log (1-ρ^2))/(2*((n+1:ℕ):ℝ)) := by
  have hr₂ : r^2 ≤ ρ^2 := by nlinarith [abs_le.mp hr,sq_abs r]
  have hρarg : 0 < 1-ρ^2 := by nlinarith
  have hLog : Real.log (1-ρ^2) ≤ Real.log (1-r^2) :=
    Real.log_le_log hρarg (by linarith)
  have hN : 0 < ((n+1:ℕ):ℝ) := by positivity
  have hNat : ((n-2:ℕ):ℝ)=(n:ℝ)-2 := by rw [Nat.cast_sub hn];norm_num
  have hid : ((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ))*Real.log (1-r^2)=
      Real.log (1-r^2)/2+(-3*Real.log (1-r^2))/(2*((n+1:ℕ):ℝ)) := by
    rw [hNat]
    simp only [Nat.cast_add,Nat.cast_one]
    field_simp
    ring
  rw [hid]
  have hd := div_le_div_of_nonneg_right (by linarith :
    -3*Real.log (1-r^2) ≤ -3*Real.log (1-ρ^2)) (by positivity : 0 ≤ 2*((n+1:ℕ):ℝ))
  exact add_le_add le_rfl hd

theorem amplitudeEntropyCorrection_eventually_le {ρ ε : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,∀ r : ℝ,|r| ≤ ρ →
      ((n-2:ℕ):ℝ)/(2*((n+1:ℕ):ℝ))*Real.log (1-r^2) ≤ Real.log (1-r^2)/2+ε := by
  have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (-3*Real.log (1-ρ^2)/2)
  have ht' : Tendsto (fun n : ℕ => (-3*Real.log (1-ρ^2))/(2*((n+1:ℕ):ℝ))) atTop (𝓝 (0:ℝ)) := by
    convert ht using 1
    · funext n
      simp only [Nat.cast_add,Nat.cast_one]
      field_simp
    · ring
  filter_upwards [ht'.eventually (gt_mem_nhds hε),eventually_ge_atTop 2] with n hn hdim
  intro r hr
  exact (amplitudeEntropyCorrection_le hdim hρ0 hρ1 hr).trans (by linarith)

/-- The actual restricted partition is bounded by its compact latitude
part plus the actual polar partition, with a literal indicator cover. -/
theorem amplitudeRestrictedPartition_le_compact_add_polar (μ : FiniteMixture) (β J δ q₁ q₂ ρ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (A : Set ℝ) (hA : MeasurableSet A) (D : BankDisorder n μ) :
    amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (overlapRegion x A) D ≤ amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s
        (overlapRegion x (A∩Icc (-ρ) ρ)) D+
      amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (poleRegion x ρ) D := by
  let V := amplitudeSourcePotential μ β J δ q₁ q₂ x p₀ s D
  let E := overlapRegion x A
  let C := overlapRegion x (A∩Icc (-ρ) ρ)
  let P := poleRegion x ρ
  have hE : MeasurableSet E := overlapRegion_measurable x hA
  have hC : MeasurableSet C := overlapRegion_measurable x (hA.inter measurableSet_Icc)
  have hP : MeasurableSet P := poleRegion_measurable x ρ
  have hi := partition_integrand_integrable (by omega : 1 ≤ n+1) 1
    (amplitudeSourcePotential_continuous μ β J δ q₁ q₂ x p₀ s D)
  have hcover : ∀ u : Vector (n+1),E.indicator (fun u => Real.exp (1*V u)) u ≤ C.indicator (fun u => Real.exp (1*V u)) u+P.indicator (fun u => Real.exp (1*V u)) u := by
    intro u
    by_cases hu : u∈E
    · rw [indicator_of_mem hu]
      by_cases hc : |overlap u x| ≤ ρ
      · have hc' : u∈C := ⟨hu,abs_le.mp hc⟩
        rw [indicator_of_mem hc']
        exact le_add_of_nonneg_right (indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
      · have hp : u∈P := (le_of_lt (lt_of_not_ge hc))
        rw [indicator_of_mem hp]
        exact le_add_of_nonneg_left (indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
    · rw [indicator_of_notMem hu]
      exact add_nonneg (indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
        (indicator_nonneg (fun u _ => (Real.exp_pos _).le) u)
  have hh := integral_mono (hi.indicator hE) ((hi.indicator hC).add (hi.indicator hP)) hcover
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi.indicator hC) (hi.indicator hP),integral_indicator hE,integral_indicator hC,integral_indicator hP] at hh
  simp_rw [amplitudeRestrictedPartition_eq_partitionOn]
  exact hh

theorem amplitudePartition_le_compact_add_polar (μ : FiniteMixture) (β J δ q₁ q₂ ρ : ℝ)
    (x : Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (D : BankDisorder n μ) :
    amplitudePartition μ β J δ q₁ q₂ x (latitudeFrameAt x) p₀ s D ≤ amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (overlapRegion x (Icc (-ρ) ρ)) D+
      amplitudeRestrictedPartition μ β J δ q₁ q₂ x p₀ s (poleRegion x ρ) D := by
  have hh := amplitudeRestrictedPartition_le_compact_add_polar μ β J δ q₁ q₂ ρ x p₀ s univ MeasurableSet.univ D
  simpa only [overlapRegion,mem_univ,Set.ofPred_true,Set.univ_inter,amplitudeRestrictedPartition,Measure.restrict_univ,
    amplitudePartition,Nat.cast_add,Nat.cast_one] using hh

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
