-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitude
public import SlowEquilibration.SphericalKacRiceGluing
public import SlowEquilibration.RoundSphereChartIntegral

@[expose] public section

/-!
# Genuine spherical integration by latitude through the round chart

The formula is derived from actual normalized round area and ordinary polar
integration. Its radial coordinate r corresponds to latitude q=1-r²/2. The
chart density is retained explicitly, so no entropy approximation or assumed
spherical disintegration enters the formula.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter Metric
open SphereChartVolume SphereVolume SphericalKacRiceGluing
open scoped Topology ENNReal InnerProductSpace

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The canonical tangent frame of the independently constructed round chart. -/
def latitudeChartFrame (n : ℕ) : Vector n →ₗᵢ[ℝ] Vector (n+1) where
  toFun x := chartAmbientIsometry n (WithLp.toLp 2 (x,(0 : ℝ)))
  map_add' x y := by
    rw [← map_add]
    congr 1
    change WithLp.toLp 2 (x+y,(0 : ℝ)) = WithLp.toLp 2 (x+y,(0 : ℝ)+0)
    simp
  map_smul' t x := by
    rw [← map_smul]
    congr 1
    change WithLp.toLp 2 (t • x,(0 : ℝ)) = WithLp.toLp 2 (t • x,t*(0 : ℝ))
    simp
  norm_map' x := by
    change ‖chartAmbientIsometry n (WithLp.toLp 2 (x,(0 : ℝ)))‖ = ‖x‖
    rw [(chartAmbientIsometry n).norm_map,WithLp.norm_toLp_fst]

def latitudeChartPole (n : ℕ) : Vector (n+1) :=
  Real.sqrt ((n+1 : ℕ) : ℝ) • chartAmbientIsometry n (WithLp.toLp 2 (0,(1 : ℝ)))

theorem latitudeChartPole_norm_sq (n : ℕ) :
    ‖latitudeChartPole n‖^2=((n+1 : ℕ) : ℝ) := by
  rw [latitudeChartPole,norm_smul,(chartAmbientIsometry n).norm_map,WithLp.norm_toLp_snd,
    norm_one,mul_one,Real.norm_eq_abs,sq_abs,Real.sq_sqrt (Nat.cast_nonneg (n+1))]

theorem latitudeChartFrame_orthogonal (n : ℕ) (x : Vector n) :
    inner ℝ (latitudeChartFrame n x) (latitudeChartPole n)=0 := by
  change inner ℝ (chartAmbientIsometry n (WithLp.toLp 2 (x,(0 : ℝ))))
    (Real.sqrt ((n+1 : ℕ) : ℝ) • chartAmbientIsometry n (WithLp.toLp 2 (0,(1 : ℝ))))=0
  rw [real_inner_smul_right,(chartAmbientIsometry n).inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- The radial round-chart parametrization is precisely the previously
constructed normalized latitude parametrization. -/
theorem manuscriptChart_radial_eq_latitudeMap {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr2 : r < 2) (u : sphere (0 : Vector n) 1) :
    manuscriptChart n (r • (u : Vector n)) =
      latitudeMap (latitudeChartPole n) (latitudeChartFrame n) (1-r^2/2)
        (Real.sqrt (n : ℝ) • (u : Vector n)) := by
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hs : 0 ≤ 1-r^2/4 := by nlinarith
  have hq : 0 ≤ 1-(1-r^2/2)^2 := by nlinarith [mul_nonneg (sq_nonneg r) hs]
  have hcoef : Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-(1-r^2/2)^2))*Real.sqrt (n : ℝ) =
      Real.sqrt ((n+1 : ℕ) : ℝ)*(Real.sqrt (1-r^2/4)*r) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by positivity),Real.sq_sqrt hnr.le,
      mul_pow,Real.sq_sqrt (Nat.cast_nonneg (n+1)),mul_pow,Real.sq_sqrt hs]
    field_simp
    ring
  change Real.sqrt ((n+1 : ℕ) : ℝ) • chartAmbientIsometry n (sphereChartND (r • (u : Vector n))) =
    (1-r^2/2) • (Real.sqrt ((n+1 : ℕ) : ℝ) • chartAmbientIsometry n (WithLp.toLp 2 (0,(1 : ℝ))))+
      Real.sqrt (((n+1 : ℕ) : ℝ)/(n : ℝ)*(1-(1-r^2/2)^2)) •
        chartAmbientIsometry n (WithLp.toLp 2 (Real.sqrt (n : ℝ) • (u : Vector n),(0 : ℝ)))
  apply (chartAmbientIsometry n).symm.injective
  simp only [map_add,map_smul,LinearIsometryEquiv.symm_apply_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp only [WithLp.ofLp_smul,WithLp.ofLp_add,sphereChartND,
      Prod.smul_fst,Prod.fst_add,smul_zero,zero_add]
    have hnorm : ‖r • (u : Vector n)‖=r := by
      simp [norm_smul,Real.norm_of_nonneg hr.le]
    simp only [sphereChartScaleND,hnorm,smul_smul]
    congr 1
    exact hcoef.symm
  · simp only [WithLp.ofLp_smul,WithLp.ofLp_add,sphereChartND,
      Prod.smul_snd,Prod.snd_add,smul_eq_mul,mul_one]
    have hnorm : ‖r • (u : Vector n)‖=r := by
      simp [norm_smul,Real.norm_of_nonneg hr.le]
    rw [hnorm]
    ring

/-- The full actual uniform sphere integral in its ordinary Lambert chart. -/
theorem sphereLaw_lintegral_lambert {n : ℕ} (hn : 1 ≤ n)
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sphereLaw (n+1)) =
      ((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
        ∫⁻ x : Vector n in ball 0 2, ENNReal.ofReal (sphereChartWeightND x)*F (manuscriptChart n x) := by
  have hfull : (sphereLaw (n+1)).restrict (manuscriptChart n '' ball (0 : Vector n) 2) = sphereLaw (n+1) := by
    change (SphericalAging.SphereInitialLaw.sphereLaw (n+1)).restrict _ =
      SphericalAging.SphereInitialLaw.sphereLaw (n+1)
    rw [sphereLaw_eq_normalized_roundVolume,Measure.restrict_smul,
      manuscriptRoundVolume_restrict_full_chart n hn]
  rw [← hfull,sphereLaw_restrict_manuscriptChart isOpen_ball.measurableSet (Subset.rfl),
    lintegral_smul_measure,lintegral_map hF (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable]
  have hdens : (volume.restrict (ball (0 : Vector n) 2)).withDensity
      (fun x => ENNReal.ofReal (Real.sqrt (sphereChartGramND x).det)) =
      (volume.restrict (ball (0 : Vector n) 2)).withDensity
        (fun x => ENNReal.ofReal (sphereChartWeightND x)) := by
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
    rw [sphereChartWeightND_eq_sqrt_gram (by simpa using hx)]
  have hFm : Measurable (fun x : Vector n => F (manuscriptChart n x)) :=
    hF.comp (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable
  simp only [smul_eq_mul]
  rw [hdens,lintegral_withDensity_eq_lintegral_mul _
    sphereChartWeightND_measurable.ennreal_ofReal hFm]
  rfl

def latitudeChartWeight (n : ℕ) (r : ℝ) : ℝ :=
  (Real.sqrt (1-r^2/4))^n/(Real.sqrt (1-r^2/4))^2

theorem latitudeChartWeight_measurable (n : ℕ) : Measurable (latitudeChartWeight n) := by
  unfold latitudeChartWeight
  fun_prop

theorem sphereChartWeightND_radial {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (u : sphere (0 : Vector n) 1) :
    sphereChartWeightND (r • (u : Vector n))=latitudeChartWeight n r := by
  simp [sphereChartWeightND,sphereChartScaleND,latitudeChartWeight,norm_smul,Real.norm_of_nonneg hr]

/-- The exact coarea entropy factor. The additional factor r is the absolute
Jacobian of the change of latitude q=1-r²/2. -/
theorem latitudeChartWeight_radial_entropy {n : ℕ} (hn : 2 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr2 : r < 2) :
    r^(n-1)*latitudeChartWeight n r =
      r*(Real.sqrt (1-(1-r^2/2)^2))^(n-2) := by
  have hspos : 0 < Real.sqrt (1-r^2/4) := Real.sqrt_pos.mpr (by nlinarith)
  have hssq : (Real.sqrt (1-r^2/4))^2=1-r^2/4 := Real.sq_sqrt (by nlinarith)
  have he : 1-(1-r^2/2)^2=(r*Real.sqrt (1-r^2/4))^2 := by
    rw [mul_pow,hssq]
    ring
  have hs : Real.sqrt (1-(1-r^2/2)^2)=r*Real.sqrt (1-r^2/4) := by
    rw [he,Real.sqrt_sq (mul_pos hr hspos).le]
  obtain ⟨k,hk⟩ : ∃ k : ℕ, n=k+2 := ⟨n-2,by omega⟩
  subst n
  have hk1 : k+2-1=k+1 := by omega
  rw [hs,hk1,Nat.add_sub_cancel]
  unfold latitudeChartWeight
  have hc : (Real.sqrt (1-r^2/4))^(k+2)/(Real.sqrt (1-r^2/4))^2 =
      (Real.sqrt (1-r^2/4))^k := by
    rw [pow_add,mul_div_cancel_right₀ _ (pow_ne_zero 2 hspos.ne')]
  rw [hc,pow_succ,mul_pow]
  ring

/-- An exact latitude disintegration in the radial coordinate of the Lambert
chart. Both measures and the density are independently constructed from
ordinary volume, and the omitted pole has zero actual sphere measure. -/
theorem sphereLaw_lintegral_latitude_radial {n : ℕ} (hn : 1 ≤ n)
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sphereLaw (n+1)) =
      ((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
        ∫⁻ r : Ioi (0 : ℝ), {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
          (fun s => ENNReal.ofReal (latitudeChartWeight n s)*
            ∫⁻ u : sphere (0 : Vector n) 1, F (manuscriptChart n ((s : ℝ) • (u : Vector n)))
              ∂unitAngular (Vector n)) r ∂haarRadius (Vector n) := by
  let : NeZero n := ⟨by omega⟩
  rw [sphereLaw_lintegral_lambert hn F hF,← lintegral_indicator isOpen_ball.measurableSet]
  have hm : Measurable ((ball (0 : Vector n) 2).indicator
      (fun x => ENNReal.ofReal (sphereChartWeightND x)*F (manuscriptChart n x))) :=
    (sphereChartWeightND_measurable.ennreal_ofReal.mul
      (hF.comp (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable)).indicator isOpen_ball.measurableSet
  rw [polar_lintegral_normalized _ hm]
  congr 1
  apply lintegral_congr
  intro r
  by_cases hr : (r : ℝ)<2
  · rw [Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr)]
    have he : ∀ u : sphere (0 : Vector n) 1,
        (r : ℝ) • (u : Vector n) ∈ ball 0 2 := by
      intro u
      simpa [norm_smul,Real.norm_of_nonneg r.property.le] using hr
    simp_rw [Set.indicator_of_mem (he _),sphereChartWeightND_radial r.property.le]
    exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr)]
    have he : ∀ u : sphere (0 : Vector n) 1,
        (r : ℝ) • (u : Vector n) ∉ ball 0 2 := by
      intro u
      simpa [norm_smul,Real.norm_of_nonneg r.property.le] using hr
    simp_rw [Set.indicator_of_notMem (he _)]
    exact lintegral_zero

/-- Exact spherical coarea with the latitude entropy density displayed. The
scalar base measure is ordinary Lebesgue measure on the positive radius ray;
the factor r is exactly |dq/dr| for q=1-r²/2. -/
theorem sphereLaw_lintegral_latitude_entropy {n : ℕ} (hn : 2 ≤ n)
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sphereLaw (n+1)) =
      (((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
        (volume : Measure (Vector n)).toSphere univ) *
        ∫⁻ r : Ioi (0 : ℝ), {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
          (fun s => ENNReal.ofReal ((s : ℝ)*(Real.sqrt (1-(1-(s : ℝ)^2/2)^2))^(n-2))*
            ∫⁻ u : sphere (0 : Vector n) 1, F (manuscriptChart n ((s : ℝ) • (u : Vector n)))
              ∂unitAngular (Vector n)) r ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
  let : NeZero n := ⟨by omega⟩
  have hang : Measurable (fun r : Ioi (0 : ℝ) =>
      ∫⁻ u : sphere (0 : Vector n) 1, F (manuscriptChart n ((r : ℝ) • (u : Vector n)))
        ∂unitAngular (Vector n)) := by
    apply Measurable.lintegral_prod_right
    exact hF.comp ((RoundSphereChartIntegral.manuscriptChart_continuous n).measurable.comp
      (measurable_fst.subtype_val.smul measurable_snd.subtype_val))
  have hm : Measurable (fun r : Ioi (0 : ℝ) => {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
      (fun s => ENNReal.ofReal (latitudeChartWeight n s)*
        ∫⁻ u : sphere (0 : Vector n) 1, F (manuscriptChart n ((s : ℝ) • (u : Vector n)))
          ∂unitAngular (Vector n)) r) :=
    (((latitudeChartWeight_measurable n).comp measurable_subtype_coe).ennreal_ofReal.mul hang).indicator
      (measurableSet_lt measurable_subtype_coe measurable_const)
  rw [sphereLaw_lintegral_latitude_radial (by omega) F hF,
    haarRadius,lintegral_smul_measure,Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hm]
  simp only [smul_eq_mul,← mul_assoc]
  congr 1
  apply lintegral_congr
  intro r
  dsimp only [Pi.mul_apply]
  by_cases hr : (r : ℝ)<2
  · rw [Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      ← mul_assoc,← ENNReal.ofReal_mul (pow_nonneg r.property.le _)]
    rw [show Module.finrank ℝ (Vector n)=n from by simp [Vector,SphericalAging.FiniteModel.Vector],
      latitudeChartWeight_radial_entropy hn r.property hr]
  · rw [Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),mul_zero]

/-- Identification of the actual angular slice with the actual normalized
latitude law, rather than a new measure defined by the desired identity. -/
theorem lambert_angular_eq_latitude {n : ℕ} (hn : 1 ≤ n)
    {r : ℝ} (hr : 0 < r) (hr2 : r < 2)
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ u : sphere (0 : Vector n) 1, F (manuscriptChart n (r • (u : Vector n)))
      ∂unitAngular (Vector n)) =
      ∫⁻ v, F v ∂latitudeLaw (latitudeChartPole n) (latitudeChartFrame n) (1-r^2/2) := by
  let : NeZero n := ⟨by omega⟩
  rw [latitudeLaw,lintegral_map hF
    (latitudeMap_continuous (latitudeChartPole n) (latitudeChartFrame n) (1-r^2/2)).measurable]
  rw [show sphereLaw n = (unitAngular (Vector n)).map
      (fun u : sphere (0 : Vector n) 1 => Real.sqrt (n : ℝ) • (u : Vector n)) from
    SphereVolume.sphereLaw_eq_normalized_angular n hn]
  have hm : Measurable (fun x =>
      F (latitudeMap (latitudeChartPole n) (latitudeChartFrame n) (1-r^2/2) x)) :=
    hF.comp (latitudeMap_continuous _ _ _).measurable
  rw [lintegral_map hm (by fun_prop)]
  apply lintegral_congr
  intro u
  rw [manuscriptChart_radial_eq_latitudeMap hn hr hr2]

/-- Full actual spherical disintegration with its precise entropy density and
the literal normalized latitude laws used by the interpolation bound. -/
theorem sphereLaw_lintegral_latitudeLaw {n : ℕ} (hn : 2 ≤ n)
    (F : Vector (n+1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂sphereLaw (n+1)) =
      (((volume : Measure (WithLp 2 (Vector n × ℝ))).toSphere univ)⁻¹ *
        (volume : Measure (Vector n)).toSphere univ) *
        ∫⁻ r : Ioi (0 : ℝ), {s : Ioi (0 : ℝ) | (s : ℝ)<2}.indicator
          (fun s => ENNReal.ofReal ((s : ℝ)*(Real.sqrt (1-(1-(s : ℝ)^2/2)^2))^(n-2))*
            ∫⁻ v, F v ∂latitudeLaw (latitudeChartPole n) (latitudeChartFrame n) (1-(s : ℝ)^2/2)) r
          ∂(volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
  rw [sphereLaw_lintegral_latitude_entropy hn F hF]
  congr 1
  apply lintegral_congr
  intro r
  by_cases hr : (r : ℝ)<2
  · rw [Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_mem (show r ∈ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      lambert_angular_eq_latitude (by omega) r.property hr F hF]
  · rw [Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr),
      Set.indicator_of_notMem (show r ∉ {s : Ioi (0 : ℝ) | (s : ℝ)<2} from hr)]

end SlowEquilibration.SphericalModel
