-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPLatitudeCoareaChange
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-! The measure-level Jacobian for the manuscript's latitude coordinate.
Unlike the earlier continuous real-integral substitution, this applies to
any nonnegative coarea density. It is the scalar bridge needed to turn the
existing exact radial spherical disintegration into a latitude band. -/

namespace SlowEquilibration.SphericalTAPLatitudeLIntegralChange
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalTAPLatitudeCoareaChange
open scoped ENNReal
set_option autoImplicit false

/-- On nonnegative chart radii, physical latitude decreases. -/
theorem radialLatitude_antitoneOn_Icc {a b : ℝ} (ha : 0 ≤ a) :
    AntitoneOn radialLatitude (Icc a b) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := ha.trans hx.1
  have hy0 : 0 ≤ y := ha.trans hy.1
  have hprod : 0 ≤ (y-x)*(y+x) :=
    mul_nonneg (sub_nonneg.mpr hxy) (add_nonneg hy0 hx0)
  dsimp [radialLatitude]
  nlinarith

/-- Exact nonnegative-integral substitution for `q=1-r²/2`. The factor
`r` is the actual absolute Jacobian, with no regularity condition on `F`. -/
theorem radialLatitude_lintegral_Icc {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (F : ℝ → ℝ≥0∞) :
    (∫⁻ q in Icc (radialLatitude b) (radialLatitude a), F q) =
      ∫⁻ r in Icc a b, ENNReal.ofReal r * F (radialLatitude r) := by
  have hanti : AntitoneOn radialLatitude (Icc a b) :=
    radialLatitude_antitoneOn_Icc ha
  have hcont : ContinuousOn radialLatitude (Icc a b) := by
    unfold radialLatitude
    fun_prop
  have himage : radialLatitude '' Icc a b =
      Icc (radialLatitude b) (radialLatitude a) :=
    hcont.image_Icc_of_antitoneOn hab hanti
  have hderiv : ∀ r ∈ Icc a b,
      HasDerivWithinAt radialLatitude (-r) (Icc a b) r := by
    intro r _
    exact (radialLatitude_hasDerivAt r).hasDerivWithinAt
  have hchange := lintegral_image_eq_lintegral_deriv_mul_of_antitoneOn
    measurableSet_Icc hderiv hanti F
  rw [himage] at hchange
  simpa only [neg_neg] using hchange

/-- Exact inverse image of a latitude interval on the nonnegative radial
ray; no approximate shell enlargement is involved. -/
theorem radialLatitude_mem_Icc_iff {a b r : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hr : 0 ≤ r) :
    radialLatitude r ∈ Icc (radialLatitude b) (radialLatitude a) ↔
      r ∈ Icc a b := by
  have hb : 0 ≤ b := ha.trans hab
  constructor
  · intro h
    have hrb : r ≤ b := (sq_le_sq₀ hr hb).mp (by
      dsimp [radialLatitude] at h
      nlinarith [h.1])
    have har : a ≤ r := (sq_le_sq₀ ha hr).mp (by
      dsimp [radialLatitude] at h
      nlinarith [h.2])
    exact ⟨har,hrb⟩
  · intro h
    have hsqa : a^2 ≤ r^2 := (sq_le_sq₀ ha hr).mpr h.1
    have hsqb : r^2 ≤ b^2 := (sq_le_sq₀ hr hb).mpr h.2
    dsimp [radialLatitude]
    constructor <;> nlinarith

/-- The positive Lambert-chart radius corresponding to a physical latitude. -/
def latitudeRadius (q : ℝ) : ℝ := Real.sqrt (2*(1-q))

theorem latitudeRadius_sq (q : ℝ) (hq : q ≤ 1) :
    latitudeRadius q ^ 2 = 2*(1-q) := by
  unfold latitudeRadius
  exact Real.sq_sqrt (by linarith)

theorem radialLatitude_latitudeRadius (q : ℝ) (hq : q ≤ 1) :
    radialLatitude (latitudeRadius q) = q := by
  unfold radialLatitude
  rw [latitudeRadius_sq q hq]
  ring

theorem latitudeRadius_nonneg (q : ℝ) : 0 ≤ latitudeRadius q :=
  Real.sqrt_nonneg _

theorem latitudeRadius_pos (q : ℝ) (hq : q < 1) :
    0 < latitudeRadius q := by
  unfold latitudeRadius
  exact Real.sqrt_pos.mpr (by linarith)

/-- Every nonnegative coarea density on a symmetric latitude band admits
the exact radial representation with the physical Jacobian. -/
theorem symmetric_latitude_lintegral_change
    (center width : ℝ) (hwidth : 0 ≤ width)
    (hupper : center+width ≤ 1) (F : ℝ → ℝ≥0∞) :
    (∫⁻ q in Icc (center-width) (center+width), F q) =
      ∫⁻ r in Icc (latitudeRadius (center+width))
          (latitudeRadius (center-width)),
        ENNReal.ofReal r * F (radialLatitude r) := by
  have hlow : center-width ≤ 1 := by linarith
  have horder : latitudeRadius (center+width) ≤
      latitudeRadius (center-width) := by
    unfold latitudeRadius
    apply Real.sqrt_le_sqrt
    linarith
  have h := radialLatitude_lintegral_Icc
    (latitudeRadius_nonneg (center+width)) horder F
  rw [radialLatitude_latitudeRadius (center-width) hlow,
      radialLatitude_latitudeRadius (center+width) hupper] at h
  exact h

/-- A radial interval inside the positive chart ray has the same integral
under the chart's subtype/comap volume as under ordinary Lebesgue volume. -/
theorem positive_radial_subtype_lintegral_Icc
    {a b : ℝ} (ha : 0 < a) (F : ℝ → ℝ≥0∞) :
    (∫⁻ r : Ioi (0:ℝ) in {s | (s:ℝ) ∈ Icc a b}, F r
      ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ))) =
      ∫⁻ r in Icc a b, F r ∂volume := by
  have hset : (Subtype.val : Ioi (0:ℝ) → ℝ) ''
      {s | (s:ℝ) ∈ Icc a b} = Icc a b := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact hs
    · intro hr
      exact ⟨⟨r,ha.trans_le hr.1⟩,hr,rfl⟩
  rw [setLIntegral_subtype measurableSet_Ioi, hset]

/-- The two indicators in the actual radial spherical coarea formula cut
out exactly the radial preimage of a closed latitude band. -/
theorem radial_subtype_band_lintegral_Icc
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2)
    (F : ℝ → ℝ≥0∞) :
    (∫⁻ s : Ioi (0:ℝ),
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => (Icc (radialLatitude b) (radialLatitude a)).indicator
          (fun _ => F (t:ℝ)) (radialLatitude t)) s
      ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ))) =
      ∫⁻ r in Icc a b, F r ∂volume := by
  have hpoint (s : Ioi (0:ℝ)) :
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => (Icc (radialLatitude b) (radialLatitude a)).indicator
          (fun _ => F (t:ℝ)) (radialLatitude t)) s =
      {t : Ioi (0:ℝ) | (t:ℝ) ∈ Icc a b}.indicator
        (fun t => F (t:ℝ)) s := by
    have hiff := radialLatitude_mem_Icc_iff ha.le hab s.property.le
    by_cases hs : (s:ℝ) ∈ Icc a b
    · have h2 : (s:ℝ) < 2 := lt_of_le_of_lt hs.2 hb
      simp only [Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from h2),
        Set.indicator_of_mem (hiff.mpr hs),
        Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ) ∈ Icc a b} from hs)]
    · have hq : radialLatitude (s:ℝ) ∉
          Icc (radialLatitude b) (radialLatitude a) := fun h => hs (hiff.mp h)
      by_cases h2 : (s:ℝ) < 2
      · simp only [Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from h2),
          Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ) ∈ Icc a b} from hs)]
      · simp only [Set.indicator_of_notMem
          (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ)<2} from h2),
          Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ) ∈ Icc a b} from hs)]
  simp_rw [hpoint]
  have hmeas : MeasurableSet
      {t : Ioi (0:ℝ) | (t:ℝ) ∈ Icc a b} :=
    measurableSet_Icc.preimage measurable_subtype_coe
  rw [lintegral_indicator hmeas]
  exact positive_radial_subtype_lintegral_Icc ha F

/-- The entire radial subtype integral in the spherical coarea formula
becomes the latitude integral. This includes both radial cutoff indicators
and the physical Jacobian, for an arbitrary nonnegative latitude density. -/
theorem radial_subtype_band_lintegral_eq_latitude
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2)
    (G : ℝ → ℝ≥0∞) :
    (∫⁻ s : Ioi (0:ℝ),
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => (Icc (radialLatitude b) (radialLatitude a)).indicator
          (fun q => ENNReal.ofReal (t:ℝ) * G q) (radialLatitude t)) s
      ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ))) =
      ∫⁻ q in Icc (radialLatitude b) (radialLatitude a), G q ∂volume := by
  calc
    _ = ∫⁻ r in Icc a b,
          ENNReal.ofReal r * G (radialLatitude r) ∂volume := by
            exact radial_subtype_band_lintegral_Icc ha hab hb
              (fun r => ENNReal.ofReal r * G (radialLatitude r))
    _ = _ := (radialLatitude_lintegral_Icc ha.le hab G).symm

/-- Exact latitude-band coarea for the genuine restricted spherical Gibbs
partition. The right side uses the true conditional spherical latitude
density, including its `(n-2)` transverse entropy power. -/
theorem partitionOn_radial_band_eq_latitude
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 2) :
    ENNReal.ofReal (partitionOn β H
      (overlapRegion u (Icc (radialLatitude b) (radialLatitude a)))) =
      latitudeNormalization n *
        ∫⁻ q in Icc (radialLatitude b) (radialLatitude a),
          ENNReal.ofReal (latitudeDensityPartition n β H u q) ∂volume := by
  rw [partitionOn_latitude_coarea hn β hH u hu measurableSet_Icc]
  congr 1
  calc
    _ = ∫⁻ s : Ioi (0:ℝ),
        {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
          (fun t => (Icc (radialLatitude b) (radialLatitude a)).indicator
            (fun q => ENNReal.ofReal (t:ℝ) *
              ENNReal.ofReal (latitudeDensityPartition n β H u q))
            (radialLatitude t)) s
        ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ)) := by
          apply lintegral_congr
          intro s
          by_cases hs : (s:ℝ) < 2
          · rw [Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs),
                Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs)]
            by_cases hq : radialLatitude (s:ℝ) ∈
                Icc (radialLatitude b) (radialLatitude a)
            · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
              exact ENNReal.ofReal_mul s.property.le
            · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs),
                Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs)]
    _ = _ := radial_subtype_band_lintegral_eq_latitude ha hab hb
      (fun q => ENNReal.ofReal (latitudeDensityPartition n β H u q))

/-- Exact physical spherical coarea on a symmetric latitude band about
`center`, including the true `latitudeNormalization n`. -/
theorem partitionOn_symmetric_band_eq_latitude
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    {center width : ℝ} (hwidth : 0 ≤ width)
    (hbelow : -1 < center-width) (habove : center+width < 1) :
    ENNReal.ofReal (partitionOn β H
      (overlapRegion u (Icc (center-width) (center+width)))) =
      latitudeNormalization n *
        ∫⁻ q in Icc (center-width) (center+width),
          ENNReal.ofReal (latitudeDensityPartition n β H u q) ∂volume := by
  let a := latitudeRadius (center+width)
  let b := latitudeRadius (center-width)
  have hlow : center-width ≤ 1 := by linarith
  have hhigh : center+width ≤ 1 := habove.le
  have ha : 0 < a := latitudeRadius_pos _ habove
  have hab : a ≤ b := by
    unfold a b latitudeRadius
    apply Real.sqrt_le_sqrt
    linarith
  have hb : b < 2 := by
    have hb2 := latitudeRadius_sq (center-width) hlow
    have hb0 := latitudeRadius_nonneg (center-width)
    dsimp [b]
    nlinarith
  have h := partitionOn_radial_band_eq_latitude hn β hH u hu ha hab hb
  rw [radialLatitude_latitudeRadius (center-width) hlow,
      radialLatitude_latitudeRadius (center+width) hhigh] at h
  exact h

/-- Ordinary-real form of the exact coarea formula. The integrability
hypothesis is only the standard requirement for converting a nonnegative
Lebesgue integral from `ℝ≥0∞` to `ℝ`. -/
theorem partitionOn_symmetric_band_eq_real_integral
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    {center width : ℝ} (hwidth : 0 ≤ width)
    (hbelow : -1 < center-width) (habove : center+width < 1)
    (hden : IntegrableOn
      (latitudeDensityPartition n β H u)
      (Icc (center-width) (center+width)) volume) :
    partitionOn β H (overlapRegion u (Icc (center-width) (center+width))) =
      (latitudeNormalization n).toReal *
        ∫ q in Icc (center-width) (center+width),
          latitudeDensityPartition n β H u q ∂volume := by
  have hcoarea := partitionOn_symmetric_band_eq_latitude hn β hH u hu
    hwidth hbelow habove
  have hreal : ENNReal.ofReal
      (∫ q in Icc (center-width) (center+width),
        latitudeDensityPartition n β H u q ∂volume) =
      ∫⁻ q in Icc (center-width) (center+width),
        ENNReal.ofReal (latitudeDensityPartition n β H u q) ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hden
      (Filter.Eventually.of_forall fun q => latitudeDensityPartition_nonneg n β H u q)
  rw [← hreal] at hcoarea
  have h := congrArg ENNReal.toReal hcoarea
  rw [ENNReal.toReal_ofReal (partitionOn_nonneg β H _),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg
      (fun q => latitudeDensityPartition_nonneg n β H u q))] at h
  exact h

end
end SlowEquilibration.SphericalTAPLatitudeLIntegralChange
