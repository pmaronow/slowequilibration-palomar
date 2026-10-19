-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureDenominatorPalmTransfer
public import SlowEquilibration.SourcePureRetainedMaximumTransfer
public import SlowEquilibration.SphericalTAPHeavyBandPartitionLower
public import SlowEquilibration.SourcePhysicalPurePairRetainedNormalization
public import Mathlib.Topology.Order.LiminfLimsup

/-! A nonzero literal retained pure count and the absence of light
ordinary critical bands force a lower bound on the original partition
function. This file keeps the probabilistic count inputs explicit. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureDenominatorEvent
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalForm
open SphericalTAPCertificate SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalLightBandMark SphericalTAPHeavyBandPartitionLower
open PairConditionalDeterminantMoments
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- A nonzero selected scalar-value count supplies an actual ordinary
critical point in exactly that value window. -/
theorem retained_value_nonzero_critical_nonempty
    (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (W : Set ℝ)
    (κ C ε η E G : ℝ) (J : Disorder (n+3) μ.maxDegree)
    (hret : (sourceRetainedValueWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q) W
      κ C ε η E G J).toReal ≠ 0) :
    ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
      actualValue (centerCoefficients (mixtureCoefficients μ) Q) J u ∈ W := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let A : Set (Vector (n+3)) := {u | ‖u‖^2=(n+3:ℕ) ∧
    surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W}
  have hA : A.Nonempty := by
    by_contra hne
    have hempty : A=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : sourceRetainedValueWindowCount (n+2) c W
        κ C ε η E G J=0 := by
      unfold sourceRetainedValueWindowCount actualValueWindowCount
      change (∑' u : A, sourceSelectionMark c κ C ε η E G J u)=0
      rw [hempty]
      exact tsum_empty
    exact hret (by rw [hzero]; rfl)
  exact hA

/-- A nonlight critical point in the centered value window forces the
global partition lower bound on the exact Palm band scale. -/
theorem nonlight_pure_critical_forces_partition_lower
    (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (J : Disorder (n+3) μ.maxDegree) (u : Vector (n+3))
    (m T δ : ℝ) (I : Set ℝ) (hI : MeasurableSet I)
    (hδ : 0 ≤ δ)
    (henergy : m-T ≤ field
      (centerCoefficients (mixtureCoefficients μ) Q) J u)
    (hheavy : sourceLightBandMark (n+1) μ h.overlap_range β m δ I J u = 0) :
    δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ
      h.overlap_range β m ≤
    partition (n+3) β (field (mixtureCoefficients μ) J) := by
  let D := sourceCriticalBandScale (n+2) μ h.overlap_range β m
  have hD : 0 ≤ D := (sourceCriticalBandScale_pos (n+2) (by omega)
    μ h.overlap_range β m).le
  have hnot : ¬ overlapRestrictedPartition (mixtureCoefficients μ) β I (J,u) <
      δ*D*Real.exp (β*(field
        (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) := by
    unfold sourceLightBandMark at hheavy
    split_ifs at hheavy with hlt
    · simp at hheavy
    · exact hlt
  have hBand : δ*D*Real.exp (β*(field
      (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) ≤
      partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I) := by
    simpa only [overlapRestrictedPartition,overlapRegion] using le_of_not_gt hnot
  exact source_heavy_band_implies_partition_lower (by omega) μ Q J u I
    hI h.beta_pos.le hδ hD henergy hBand

/-- One light ordinary critical point in a Borel scalar-value window has
probability at most the original marked Kac--Rice expected count. -/
theorem pure_light_critical_probability_le_marked_count
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (W : Set ℝ) (hW : MeasurableSet W)
    (β m δ b : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let mark := sourceLightBandMark (n+1) μ hQ β m δ
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
    disorderLaw (n+3) μ.maxDegree
      {J | ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
        surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W ∧
        mark J u=1} ≤
    ∫⁻ J, actualValueWindowCount (n+2) c W mark J
      ∂disorderLaw (n+3) μ.maxDegree := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let mark := sourceLightBandMark (n+1) μ hQ β m δ
    (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
  let count := actualValueWindowCount (n+2) c W mark
  have hCount : AEMeasurable count (disorderLaw (n+3) μ.maxDegree) :=
    (actual_value_window_kacRice (n+2) (by omega) μ hQ.1 W hW mark
      (sourceLightBandMark_measurable (n+1) μ hQ β m δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) measurableSet_Icc)).1
  have hsub : {J | ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W ∧
      mark J u=1} ⊆ {J | 1 ≤ count J} := by
    rintro J ⟨u,hu,hcrit,hwin,hmark⟩
    have hterm := ENNReal.le_tsum
      (f := fun z : {z : Vector (n+3) | ‖z‖^2=(n+3:ℕ) ∧
        surfaceGradient (field c J) z=0 ∧ actualValue c J z ∈ W} =>
          mark J z) ⟨u,hu,hcrit,hwin⟩
    change 1 ≤ count J
    rw [←hmark]
    exact hterm
  apply (measure_mono hsub).trans
  simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hCount 1

/-- The finite-dimensional low-partition event is contained in the union
of a zero retained count and an ordinary light critical band. -/
theorem pure_low_partition_event_subset
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (J : Disorder (n+3) (FiniteMixture.pure p hp alpha halpha).maxDegree)
    (W : Set ℝ) (m T δ b κ C ε η E G : ℝ)
    (hWenergy : ∀ v ∈ W, m-T ≤ ((n+3:ℕ):ℝ)*v) (hδ : 0 ≤ δ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let mark := sourceLightBandMark (n+1) μ h.overlap_range β m δ
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
    partition (n+3) β (field (mixtureCoefficients μ) J) <
      δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ h.overlap_range β m →
      (sourceRetainedValueWindowCount (n+2) c W κ C ε η E G J).toReal=0 ∨
      ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
        surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W ∧ mark J u=1 := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let mark := sourceLightBandMark (n+1) μ h.overlap_range β m δ
    (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
  intro hlow
  by_cases hz : (sourceRetainedValueWindowCount (n+2) c W
      κ C ε η E G J).toReal=0
  · exact Or.inl hz
  right
  obtain ⟨u,hu,hcrit,hwin⟩ := retained_value_nonzero_critical_nonempty
    n μ Q W κ C ε η E G J hz
  refine ⟨u,hu,hcrit,hwin,?_⟩
  by_cases hlight : mark J u=1
  · exact hlight
  have hheavy : mark J u=0 := by
    unfold mark sourceLightBandMark at hlight ⊢
    split_ifs at hlight ⊢ <;> simp_all
  have henergy : m-T ≤ field c J u := by
    have hval := hWenergy _ hwin
    have hN : (((n+3:ℕ):ℝ)) ≠ 0 := by positivity
    change m-T ≤ (((n+3:ℕ):ℝ))*(field c J u/(n+3:ℕ)) at hval
    have heq : (((n+3:ℕ):ℝ))*(field c J u/(n+3:ℕ)) = field c J u := by
      field_simp
    rwa [heq] at hval
  have hpartition := nonlight_pure_critical_forces_partition_lower
    n μ h J u m T δ _ measurableSet_Icc hδ henergy hheavy
  exact False.elim ((not_lt.mpr hpartition) hlow)

/-- The manuscript's zero-center/light-band union bound at the limsup
level, with both original-disorder probabilities on the same sequence. -/
theorem pure_partition_low_limsup_of_zero_and_light_bounds
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (W : ℕ → Set ℝ) (hW : ∀ n, MeasurableSet (W n))
    (m : ℕ → ℝ) (T δ b κ C ε η E G ρ a : ℝ)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hEnergy : ∀ n : ℕ, ∀ v ∈ W n,
      m (n+1)-T ≤ ((n+3:ℕ):ℝ)*v)
    (hZero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) (FiniteMixture.pure p hp alpha halpha).maxDegree).real
      {J | (sourceRetainedValueWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients
          (FiniteMixture.pure p hp alpha halpha)) Q)
        (W n) κ C ε η E G J).toReal=0}) atTop ≤ a)
    (hLight : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualValueWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients
          (FiniteMixture.pure p hp alpha halpha)) Q)
        (W n)
        (sourceLightBandMark (n+1) (FiniteMixture.pure p hp alpha halpha)
          h.overlap_range β (m (n+1)) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (n+3) (FiniteMixture.pure p hp alpha halpha).maxDegree) ≤
        ENNReal.ofReal ρ) :
    Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) (FiniteMixture.pure p hp alpha halpha).maxDegree).real
        {J | partition (n+3) β
          (field (mixtureCoefficients (FiniteMixture.pure p hp alpha halpha)) J) <
          δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2)
            (FiniteMixture.pure p hp alpha halpha) h.overlap_range β
            (m (n+1))}) atTop ≤ a+ρ := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let zero (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceRetainedValueWindowCount (n+2) c (W n)
      κ C ε η E G J).toReal=0}
  let light (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
      surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W n ∧
      sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u=1}
  let low (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
      δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ h.overlap_range β
        (m (n+1))}
  have hpoint : ∀ n, low n ≤ zero n+light n := by
    intro n
    have hsub : {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
        δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ
          h.overlap_range β (m (n+1))} ⊆
      {J | (sourceRetainedValueWindowCount (n+2) c (W n)
        κ C ε η E G J).toReal=0} ∪
      {J | ∃ u : Vector (n+3), ‖u‖^2=(n+3:ℕ) ∧
        surfaceGradient (field c J) u=0 ∧ actualValue c J u ∈ W n ∧
        sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u=1} := by
      intro J hlow
      exact pure_low_partition_event_subset n p hp alpha halpha h J (W n)
        (m (n+1)) T δ b κ C ε η E G (hEnergy n) hδ hlow
    exact (measureReal_mono hsub (by finiteness)).trans
      (measureReal_union_le _ _)
  have hlightEventually : ∀ᶠ n : ℕ in atTop, light n ≤ ρ := by
    filter_upwards [hLight] with n hn
    have hMark := pure_light_critical_probability_le_marked_count
      n p hp alpha halpha h.overlap_range (W n) (hW n)
      β (m (n+1)) δ b
    have hEvent := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMark.trans hn)
    simpa only [light,measureReal_def,ENNReal.toReal_ofReal hρ] using hEvent
  have hEventual : ∀ᶠ n : ℕ in atTop, low n ≤ zero n+ρ := by
    filter_upwards [hlightEventually] with n hn
    exact (hpoint n).trans (add_le_add (le_refl _) hn)
  have hLowCob : IsCoboundedUnder (· ≤ ·) atTop low :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hSumB : IsBoundedUnder (· ≤ ·) atTop (fun n => zero n+ρ) :=
    isBoundedUnder_of ⟨1+ρ,fun n => by
      have hz : zero n ≤ 1 := measureReal_le_one
      linarith⟩
  have hLim : Filter.limsup low atTop ≤
      Filter.limsup (fun n => zero n+ρ) atTop :=
    limsup_le_limsup hEventual hLowCob hSumB
  have hzL : IsBoundedUnder (· ≥ ·) atTop zero :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hzB : IsBoundedUnder (· ≤ ·) atTop zero :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hcL : IsCoboundedUnder (· ≤ ·) atTop (fun _n : ℕ => ρ) :=
    isCoboundedUnder_le_of_le atTop (fun _n => hρ)
  have hcB : IsBoundedUnder (· ≤ ·) atTop (fun _n : ℕ => ρ) :=
    isBoundedUnder_of ⟨ρ,fun _n => le_refl ρ⟩
  have hAdd := limsup_add_le hzL hzB hcL hcB
  simp only [limsup_const] at hAdd
  have hResult := hLim.trans (hAdd.trans (add_le_add hZero (le_refl ρ)))
  simpa only [low,zero,limsup_const] using hResult

end
end SlowEquilibration.SphericalPureDenominatorEvent
