-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbsMass
public import SlowEquilibration.SphericalLatitudeTransport
public import SlowEquilibration.SphericalLatitudeNormalization

@[expose] public section

/-! Deterministic latitude Laplace estimates for actual restricted spherical
partition integrals. The integration formula is the genuine normalized round
volume disintegration, rather than an assumed coarea or pressure asymptotic. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def overlapRegion {N : ℕ} (u : Vector N) (A : Set ℝ) : Set (Vector N) :=
  {x | overlap x u ∈ A}

theorem overlapRegion_measurable {N : ℕ} (u : Vector N) {A : Set ℝ}
    (hA : MeasurableSet A) : MeasurableSet (overlapRegion u A) :=
  hA.preimage (by unfold overlap; fun_prop)

def latitudeDensityPartition (n : ℕ) (β : ℝ) (H : Vector (n+1) → ℝ)
    (u : Vector (n+1)) (q : ℝ) : ℝ :=
  (Real.sqrt (1-q^2))^(n-2)*partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H

def latitudePartitionProfile (n : ℕ) (β : ℝ) (H : Vector (n+1) → ℝ)
    (u : Vector (n+1)) (q : ℝ) : ℝ :=
  Real.log (partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H)/((n+1 : ℕ) : ℝ)+
    ((n-2 : ℕ) : ℝ)/(2*((n+1 : ℕ) : ℝ))*Real.log (1-q^2)

theorem latitudeDensityPartition_nonneg (n : ℕ) (β : ℝ) (H : Vector (n+1) → ℝ)
    (u : Vector (n+1)) (q : ℝ) : 0 ≤ latitudeDensityPartition n β H u q := by
  apply mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

theorem latitudeDensityPartition_eq_exp_profile {n : ℕ} (hn : 1 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {q : ℝ} (hq : q ∈ Ioo (-1 : ℝ) 1) :
    latitudeDensityPartition n β H u q =
      Real.exp (((n+1 : ℕ) : ℝ)*latitudePartitionProfile n β H u q) := by
  have hqa : |q| ≤ 1 := abs_le.mpr ⟨hq.1.le,hq.2.le⟩
  have hsupport := (latitudeLaw_support hn u hu (latitudeFrameAt u)
    (latitudeFrameAt_orthogonal u hu) hqa).mono (fun _ hx => hx.1)
  have hZ := partitionAgainst_pos _ hsupport β hH
  have harg : 0 < 1-q^2 := by nlinarith [hq.1,hq.2]
  have hs : 0 < Real.sqrt (1-q^2) := Real.sqrt_pos.mpr harg
  have hp : 0 < (Real.sqrt (1-q^2))^(n-2) := pow_pos hs _
  have hN : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  have heq : ((n+1 : ℕ) : ℝ)*latitudePartitionProfile n β H u q =
      Real.log ((Real.sqrt (1-q^2))^(n-2)*partitionAgainst
        (latitudeLaw u (latitudeFrameAt u) q) β H) := by
    unfold latitudePartitionProfile
    rw [Real.log_mul hp.ne' hZ.ne', Real.log_pow, Real.log_sqrt harg.le]
    field_simp
    ring
  rw [heq,Real.exp_log (mul_pos hp hZ)]
  rfl

theorem latitude_lintegral_region_exp {n : ℕ} (hn : 1 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ)) (A : Set ℝ)
    {q : ℝ} (hq : |q| ≤ 1) :
    (∫⁻ x, (overlapRegion u A).indicator (fun x => ENNReal.ofReal (Real.exp (β*H x))) x
      ∂latitudeLaw u (latitudeFrameAt u) q) =
      A.indicator (fun q => ENNReal.ofReal (partitionAgainst (latitudeLaw u (latitudeFrameAt u) q) β H)) q := by
  have hs := latitudeLaw_support hn u hu (latitudeFrameAt u) (latitudeFrameAt_orthogonal u hu) hq
  by_cases hqA : q ∈ A
  · rw [indicator_of_mem hqA]
    unfold partitionAgainst
    rw [ofReal_integral_eq_lintegral_ofReal (partitionAgainst_integrable _
      (hs.mono fun _ hx => hx.1) β hH) (.of_forall fun _ => (Real.exp_pos _).le)]
    apply lintegral_congr_ae
    filter_upwards [hs] with x hx
    rw [indicator_of_mem (show x ∈ overlapRegion u A by change overlap x u ∈ A; rw [hx.2]; exact hqA)]
  · rw [indicator_of_notMem hqA]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [hs] with x hx
    rw [indicator_of_notMem (show x ∉ overlapRegion u A by change overlap x u ∉ A; rw [hx.2]; exact hqA)]
    simp only [Pi.zero_apply]

def radialLatitude (r : ℝ) : ℝ := 1-r^2/2

theorem radialLatitude_mem {r : ℝ} (hr : r ∈ Ioo 0 2) :
    radialLatitude r ∈ Ioo (-1 : ℝ) 1 := by
  unfold radialLatitude
  constructor <;> nlinarith [hr.1,hr.2]

/-- Exact coarea of a restricted partition, still in the actual radial
chart coordinate; its Jacobian factor r is displayed explicitly. -/
theorem partitionOn_latitude_coarea {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) :
    ENNReal.ofReal (partitionOn β H (overlapRegion u A)) =
      latitudeNormalization n * ∫⁻ r : Ioi (0 : ℝ), {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
        (fun s => A.indicator (fun q => ENNReal.ofReal
          ((s : ℝ)*latitudeDensityPartition n β H u q)) (radialLatitude s)) r
        ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
  have hB := overlapRegion_measurable u hA
  have hi : Integrable (fun x => Real.exp (β*H x)) ((sphereLaw (n+1)).restrict (overlapRegion u A)) :=
    (partition_integrand_integrable (by omega) β hH).restrict
  unfold partitionOn
  rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ => (Real.exp_pos _).le),
    ← lintegral_indicator hB]
  have hF : Measurable ((overlapRegion u A).indicator
      (fun x => ENNReal.ofReal (Real.exp (β*H x)))) := by
    have hc : Continuous (fun x : Vector (n+1) => Real.exp (β*H x)) :=
      Real.continuous_exp.comp (hH.const_mul β)
    exact hc.measurable.ennreal_ofReal.indicator hB
  rw [sphereLaw_lintegral_latitudeLaw_at hn u hu
    ((overlapRegion u A).indicator (fun x => ENNReal.ofReal (Real.exp (β*H x)))) hF]
  change latitudeNormalization n * _ = latitudeNormalization n * _
  congr 1
  apply lintegral_congr
  intro r
  by_cases hr : (r : ℝ)<2
  · have hrmem : r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} := hr
    rw [indicator_of_mem hrmem,indicator_of_mem hrmem]
    have hq := radialLatitude_mem ⟨r.property,hr⟩
    have hqa : |1-(r : ℝ)^2/2| ≤ 1 := by
      simpa only [radialLatitude] using abs_le.mpr ⟨hq.1.le,hq.2.le⟩
    rw [latitude_lintegral_region_exp (by omega) β hH u hu A hqa]
    by_cases hqA : radialLatitude r ∈ A
    · have hqA' : 1-(r : ℝ)^2/2 ∈ A := hqA
      rw [indicator_of_mem hqA,indicator_of_mem hqA']
      unfold latitudeDensityPartition radialLatitude
      rw [← ENNReal.ofReal_mul (mul_nonneg r.property.le (pow_nonneg (Real.sqrt_nonneg _) _))]
      congr 1
      ring
    · have hqA' : 1-(r : ℝ)^2/2 ∉ A := hqA
      rw [indicator_of_notMem hqA,indicator_of_notMem hqA',mul_zero]
  · have hrnot : r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} := hr
    rw [indicator_of_notMem hrnot,indicator_of_notMem hrnot]

theorem radial_chart_interval_mass :
    (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) {r : Ioi (0 : ℝ) | (r : ℝ)<2} = 2 := by
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
  have himage : (Subtype.val : Ioi (0 : ℝ) → ℝ) '' {r : Ioi (0 : ℝ) | (r : ℝ)<2} = Ioo (0 : ℝ) 2 := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.property,hr⟩
    · intro hx
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
  rw [himage,Real.volume_Ioo]
  norm_num

/-- Actual restricted-partition Laplace upper. The harmless finite chart
prefactor is retained explicitly and later absorbed in the pressure tolerance. -/
theorem partitionOn_le_latitudeDensity_upper {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) {M : ℝ}
    (hupper : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 →
      latitudeDensityPartition n β H u q ≤ Real.exp (((n+1 : ℕ) : ℝ)*M)) :
    partitionOn β H (overlapRegion u A) ≤
      4*(latitudeNormalization n).toReal*Real.exp (((n+1 : ℕ) : ℝ)*M) := by
  let R : Set (Ioi (0 : ℝ)) := {r | (r : ℝ)<2}
  have hR : MeasurableSet R := (isOpen_lt continuous_subtype_val continuous_const).measurableSet
  have hpoint : ∀ r : Ioi (0 : ℝ),
      R.indicator (fun s => A.indicator (fun q => ENNReal.ofReal
        ((s : ℝ)*latitudeDensityPartition n β H u q)) (radialLatitude s)) r ≤
      R.indicator (fun _ => ENNReal.ofReal (2*Real.exp (((n+1 : ℕ) : ℝ)*M))) r := by
    intro r
    by_cases hr : r ∈ R
    · rw [indicator_of_mem hr,indicator_of_mem hr]
      by_cases hqA : radialLatitude r ∈ A
      · rw [indicator_of_mem hqA]
        apply ENNReal.ofReal_le_ofReal
        have hd := hupper _ hqA (radialLatitude_mem ⟨r.property,hr⟩)
        calc
          _ ≤ (r : ℝ)*Real.exp (((n+1 : ℕ) : ℝ)*M) := mul_le_mul_of_nonneg_left hd r.property.le
          _ ≤ _ := mul_le_mul_of_nonneg_right (le_of_lt hr) (Real.exp_pos _).le
      · rw [indicator_of_notMem hqA]
        exact bot_le
    · rw [indicator_of_notMem hr,indicator_of_notMem hr]
  have hlin := lintegral_mono hpoint (μ := volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))
  have hconst : (∫⁻ r : Ioi (0 : ℝ), R.indicator
      (fun _ => ENNReal.ofReal (2*Real.exp (((n+1 : ℕ) : ℝ)*M))) r
      ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))) =
        ENNReal.ofReal (2*Real.exp (((n+1 : ℕ) : ℝ)*M))*2 := by
    rw [lintegral_indicator hR,lintegral_const,Measure.restrict_apply_univ,
      show (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) R=2 from radial_chart_interval_mass]
  rw [hconst] at hlin
  have hh := mul_le_mul (le_refl (latitudeNormalization n)) hlin bot_le bot_le
  rw [← partitionOn_latitude_coarea hn β hH u hu hA] at hh
  have hfinite : latitudeNormalization n*(ENNReal.ofReal (2*Real.exp (((n+1 : ℕ) : ℝ)*M))*2) ≠ ⊤ :=
    ENNReal.mul_ne_top (latitudeNormalization_ne_top n)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by norm_num))
  have ht := ENNReal.toReal_mono hfinite hh
  have hexp : 0 ≤ 2*Real.exp (((n+1 : ℕ) : ℝ)*M) := by positivity
  simp only [ENNReal.toReal_mul,ENNReal.toReal_ofNat] at ht
  rw [ENNReal.toReal_ofReal (partitionOn_nonneg β H _),ENNReal.toReal_ofReal hexp] at ht
  calc
    _ ≤ (latitudeNormalization n).toReal*(2*Real.exp (((n+1 : ℕ) : ℝ)*M)*2) := ht
    _ = _ := by ring

theorem partitionOn_le_latitudeProfile_upper {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) {M : ℝ}
    (hupper : ∀ q ∈ A, q ∈ Ioo (-1 : ℝ) 1 → latitudePartitionProfile n β H u q ≤ M) :
    partitionOn β H (overlapRegion u A) ≤
      4*(latitudeNormalization n).toReal*Real.exp (((n+1 : ℕ) : ℝ)*M) := by
  apply partitionOn_le_latitudeDensity_upper hn β hH u hu hA
  intro q hqA hq
  rw [latitudeDensityPartition_eq_exp_profile (by omega) β hH u hu hq]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hupper q hqA hq) (Nat.cast_nonneg _))

theorem radial_chart_Icc_mass {a b : ℝ} (ha : 0 < a) :
    (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) {r : Ioi (0 : ℝ) | (r : ℝ) ∈ Icc a b} =
      ENNReal.ofReal (b-a) := by
  rw [(MeasurableEmbedding.subtype_coe measurableSet_Ioi).comap_apply]
  have himage : (Subtype.val : Ioi (0 : ℝ) → ℝ) '' {r : Ioi (0 : ℝ) | (r : ℝ) ∈ Icc a b} = Icc a b := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact hr
    · intro hx
      exact ⟨⟨x,ha.trans_le hx.1⟩,hx,rfl⟩
  rw [himage,Real.volume_Icc]

/-- Actual Laplace lower on a nonzero radial interval contained in the
desired overlap band. Its strictly positive geometric prefactor is explicit. -/
theorem partitionOn_ge_latitudeDensity_lower {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2)
    (hband : ∀ r ∈ Icc a b, radialLatitude r ∈ A)
    (hlower : ∀ r ∈ Icc a b,
      Real.exp (((n+1 : ℕ) : ℝ)*M) ≤ latitudeDensityPartition n β H u (radialLatitude r)) :
    (latitudeNormalization n).toReal*a*(b-a)*Real.exp (((n+1 : ℕ) : ℝ)*M) ≤
      partitionOn β H (overlapRegion u A) := by
  let S : Set (Ioi (0 : ℝ)) := {r | (r : ℝ) ∈ Icc a b}
  let R : Set (Ioi (0 : ℝ)) := {r | (r : ℝ)<2}
  have hS : MeasurableSet S := measurableSet_Icc.preimage measurable_subtype_coe
  have hpoint : ∀ r : Ioi (0 : ℝ), S.indicator
      (fun _ => ENNReal.ofReal (a*Real.exp (((n+1 : ℕ) : ℝ)*M))) r ≤
      R.indicator (fun s => A.indicator (fun q => ENNReal.ofReal
        ((s : ℝ)*latitudeDensityPartition n β H u q)) (radialLatitude s)) r := by
    intro r
    by_cases hr : r ∈ S
    · have hr' : (r : ℝ) ∈ Icc a b := hr
      have hrR : r ∈ R := hr'.2.trans_lt hb
      rw [indicator_of_mem hr,indicator_of_mem hrR,indicator_of_mem (hband r hr')]
      apply ENNReal.ofReal_le_ofReal
      have hd := hlower r hr'
      calc
        _ ≤ (r : ℝ)*Real.exp (((n+1 : ℕ) : ℝ)*M) :=
          mul_le_mul_of_nonneg_right hr'.1 (Real.exp_pos _).le
        _ ≤ _ := mul_le_mul_of_nonneg_left hd r.property.le
    · rw [indicator_of_notMem hr]
      exact bot_le
  have hlin := lintegral_mono hpoint (μ := volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ))
  rw [lintegral_indicator hS,lintegral_const,Measure.restrict_apply_univ,
    show (volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) S=ENNReal.ofReal (b-a) from
      radial_chart_Icc_mass ha] at hlin
  have hh := mul_le_mul (le_refl (latitudeNormalization n)) hlin bot_le bot_le
  rw [← partitionOn_latitude_coarea hn β hH u hu hA] at hh
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  have haexp : 0 ≤ a*Real.exp (((n+1 : ℕ) : ℝ)*M) := mul_nonneg ha.le (Real.exp_pos _).le
  simp only [ENNReal.toReal_mul] at ht
  rw [ENNReal.toReal_ofReal haexp,ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    ENNReal.toReal_ofReal (partitionOn_nonneg β H _)] at ht
  calc
    _ = (latitudeNormalization n).toReal*((a*Real.exp (((n+1 : ℕ) : ℝ)*M))*(b-a)) := by ring
    _ ≤ _ := ht

theorem partitionOn_ge_latitudeProfile_lower {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    {A : Set ℝ} (hA : MeasurableSet A) {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2)
    (hband : ∀ r ∈ Icc a b, radialLatitude r ∈ A)
    (hlower : ∀ r ∈ Icc a b, M ≤ latitudePartitionProfile n β H u (radialLatitude r)) :
    (latitudeNormalization n).toReal*a*(b-a)*Real.exp (((n+1 : ℕ) : ℝ)*M) ≤
      partitionOn β H (overlapRegion u A) := by
  apply partitionOn_ge_latitudeDensity_lower hn β hH u hu hA ha hab hb hband
  intro r hr
  have hr' : r ∈ Ioo 0 2 := ⟨ha.trans_le hr.1,hr.2.trans_lt hb⟩
  rw [latitudeDensityPartition_eq_exp_profile (by omega) β hH u hu (radialLatitude_mem hr')]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hlower r hr) (Nat.cast_nonneg _))

/-- A genuine dimension-independent lower bound for the coarea normalizer,
obtained from the total mass one of the actual sphere probability law. -/
theorem latitudeNormalization_toReal_ge_quarter {n : ℕ} (hn : 2 ≤ n) :
    (1/4 : ℝ) ≤ (latitudeNormalization n).toReal := by
  have hh := partitionOn_le_latitudeDensity_upper hn (0 : ℝ) (H := fun _ => 0)
    continuous_const (latitudeChartPole n) (latitudeChartPole_norm_sq n) (A := univ) MeasurableSet.univ
    (M := 0) (by
      intro q _ _
      have hs : Real.sqrt (1-q^2) ≤ 1 := Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg q])
      simpa only [latitudeDensityPartition,partitionAgainst,zero_mul,mul_zero,Real.exp_zero,
        integral_const,probReal_univ,one_smul,mul_one] using
          pow_le_one₀ (n := n-2) (Real.sqrt_nonneg (1-q^2)) hs)
  have hpart : partitionOn (0 : ℝ) (fun _ : Vector (n+1) => 0)
      (overlapRegion (latitudeChartPole n) univ) = 1 := by
    simp [partitionOn,overlapRegion]
  rw [hpart,mul_zero,Real.exp_zero,mul_one] at hh
  linarith

end
end SlowEquilibration.SphericalModel
