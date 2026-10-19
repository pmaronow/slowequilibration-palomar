-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfiniteFiniteSupremum
public import SlowEquilibration.FiniteTensorMixtureConcentration
public import SlowEquilibration.GaussianConcentrationLimit

/-! Sharp aggregate mean and Borell bounds for the actual infinite tail. The
index P omits blocks 0,...,P-1, hence retains source degrees at least P+2. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory Set Filter SphericalModel
open scoped Topology RealInnerProductSpace
open PureTensorJetBounds FiniteTensorMixtureMaximum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual derivative-at-one mass of the omitted-degree tail. -/
def tailSlope (μ : InfiniteMixture) (P : ℕ) : ℝ :=
  ∑' q,((q+P+2:ℕ):ℝ)*μ.coeff (q+P+2)

def tailVariance (μ : InfiniteMixture) (P : ℕ) : ℝ :=
  ∑' q,μ.coeff (q+P+2)

theorem summable_tailSlope (μ : InfiniteMixture) (P : ℕ) :
    Summable (fun q => ((q+P+2:ℕ):ℝ)*μ.coeff (q+P+2)) := by
  have h : Summable (fun q : ℕ => (q:ℝ)*μ.coeff q) := by
    simpa only [pow_one] using μ.summable_moment (k := 1) (by omega)
  exact (summable_nat_add_iff P).2 ((summable_nat_add_iff 2).2 h)

theorem summable_tailVariance (μ : InfiniteMixture) (P : ℕ) :
    Summable (fun q => μ.coeff (q+P+2)) :=
  (summable_nat_add_iff P).2 ((summable_nat_add_iff 2).2 μ.summable_coeff)

theorem tailSlope_nonneg (μ : InfiniteMixture) (P : ℕ) : 0≤tailSlope μ P :=
  tsum_nonneg fun q => mul_nonneg (Nat.cast_nonneg _) (μ.nonneg _)

theorem tailVariance_nonneg (μ : InfiniteMixture) (P : ℕ) : 0≤tailVariance μ P :=
  tsum_nonneg fun q => μ.nonneg _

theorem tailSlope_tendsto_zero (μ : InfiniteMixture) : Tendsto (tailSlope μ) atTop (𝓝 0) := by
  let f : ℕ → ℝ := fun q => ((q+2:ℕ):ℝ)*μ.coeff (q+2)
  have hs : Summable f := summable_tailSlope μ 0
  have he (P : ℕ) : tailSlope μ P=(∑' q,f q)-∑ q∈Finset.range P,f q := by
    have h := hs.sum_add_tsum_nat_add P
    change (∑' q,f (q+P))=_
    linarith
  change Tendsto (fun P => tailSlope μ P) atTop (𝓝 0)
  simp_rw [he]
  simpa only [sub_self] using
    (show Tendsto (fun P => (∑' q,f q)-∑ q∈Finset.range P,f q) atTop
      (𝓝 ((∑' q,f q)-(∑' q,f q))) from tendsto_const_nhds.sub hs.tendsto_sum_tsum_nat)

def tailSphere {N : ℕ} (μ : InfiniteMixture) (P : ℕ) (J : Disorder N) : C(UnitSphere N,ℝ) :=
  sphereRestriction N (tailContinuous μ P J)

def tailSpherePartial {N : ℕ} (μ : InfiniteMixture) (P M : ℕ) (J : Disorder N) : C(UnitSphere N,ℝ) :=
  selectedSphereField μ (fun i : Fin M => i.val+P) J

theorem tailSpherePartial_eq {N : ℕ} (μ : InfiniteMixture) (P M : ℕ) (J : Disorder N) :
    tailSpherePartial μ P M J=sphereRestriction N
      (∑ q∈Finset.range M,blockContinuous μ (q+P) J) := by
  simp only [tailSpherePartial,selectedSphereField,map_sum]
  exact Fin.sum_univ_eq_sum_range (fun q => sphereRestriction N (blockContinuous μ (q+P) J)) M

theorem tailSpherePartial_continuous {N : ℕ} (μ : InfiniteMixture) (P M : ℕ) :
    Continuous (tailSpherePartial (N := N) μ P M) := by
  unfold tailSpherePartial selectedSphereField
  exact continuous_finsetSum _ fun i _ =>
    (sphereRestriction N).continuous.comp (blockContinuous_continuous μ (i.val+P))

theorem tailSpherePartial_tendsto_ae {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ) :
    ∀ᵐ J ∂disorderLaw N,Tendsto (fun M => tailSpherePartial μ P M J) atTop
      (𝓝 (tailSphere μ P J)) := by
  filter_upwards [summableJetDisorder_ae hN μ] with J hJ
  have hs := (summable_nat_add_iff P).2 (summable_blockContinuous_norm hN μ J hJ)
  simpa only [Function.comp_def,tailSpherePartial_eq,tailSphere,tailContinuous] using
    (sphereRestriction N).continuous.continuousAt.tendsto.comp hs.of_norm.tendsto_sum_tsum_nat

theorem tailSpherePartial_expected_norm_le {N : ℕ} (hN : 0<N)
    (μ : InfiniteMixture) (P M : ℕ) :
    (∫ J,‖tailSpherePartial μ P M J‖ ∂disorderLaw N)≤2*N*Real.sqrt (tailSlope μ P) := by
  have h := selectedSphereField_expected_norm_le hN μ (fun i : Fin M => i.val+P)
    (by intro i j hij;apply Fin.ext;change i.val+P=j.val+P at hij;omega)
  refine h.trans ?_
  gcongr
  rw [Fin.sum_univ_eq_sum_range (fun q => ((q+P+2:ℕ):ℝ)*μ.coeff (q+P+2)) M]
  exact (summable_tailSlope μ P).sum_le_tsum (Finset.range M)
    (fun q _ => mul_nonneg (Nat.cast_nonneg _) (μ.nonneg _))

theorem tailSpherePartial_mean_tendsto {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ) :
    Tendsto (fun M => ∫ J,‖tailSpherePartial μ P M J‖ ∂disorderLaw N) atTop
      (𝓝 (∫ J,‖tailSphere μ P J‖ ∂disorderLaw N)) := by
  let b : Disorder N → ℝ := fun J => ∑' q,‖blockContinuous μ (q+P) J‖
  have hi : Integrable b (disorderLaw N) := by
    apply IntegrableSummableSeries.integrable_tsum
      (fun q => (blockContinuous_integrable hN μ (q+P)).norm)
    simp only [norm_norm]
    exact (summable_nat_add_iff P).2 (summable_integral_norm_blockContinuous hN μ)
  apply tendsto_integral_of_dominated_convergence b
    (fun M => (tailSpherePartial_continuous μ P M).norm.aestronglyMeasurable) hi
  · intro M
    filter_upwards [summableJetDisorder_ae hN μ] with J hJ
    have hs := (summable_nat_add_iff P).2 (summable_blockContinuous_norm hN μ J hJ)
    rw [norm_norm,tailSpherePartial_eq]
    exact (sphereRestriction_norm_le N _).trans ((norm_sum_le _ _).trans
      (hs.sum_le_tsum (Finset.range M) (fun q _ => norm_nonneg _)))
  · exact (tailSpherePartial_tendsto_ae hN μ P).mono fun J hJ => hJ.norm

/-- The source sharp infinite-tail mean, with the actual aggregate variance
rather than a sum of individual degree square roots. -/
theorem tailSphere_expected_norm_le {N : ℕ} (hN : 0<N) (μ : InfiniteMixture) (P : ℕ) :
    (∫ J,‖tailSphere μ P J‖ ∂disorderLaw N)≤2*N*Real.sqrt (tailSlope μ P) :=
  le_of_tendsto (tailSpherePartial_mean_tendsto hN μ P)
    (.of_forall fun M => tailSpherePartial_expected_norm_le hN μ P M)

theorem tailSpherePartial_upper_tail {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (P M : ℕ) {t : ℝ} (ht : 0≤t) :
    disorderLaw N {J|2*N*Real.sqrt (tailSlope μ P)+t<‖tailSpherePartial μ P M J‖}≤
      ENNReal.ofReal (Real.exp (-t^2/(2*N*tailVariance μ P))) := by
  let p : Fin M → ℕ := fun i => i.val+P
  let d : Fin M → ℕ := fun i => p i+2
  let c : Fin M → ℝ := fun i => μ.coeff (p i+2)
  have hp : Function.Injective p := by intro i j hij;apply Fin.ext;dsimp [p] at hij;omega
  have hc : ∀ i,0≤c i := fun i => μ.nonneg _
  have hvar : (∑ i,c i)≤tailVariance μ P := by
    change (∑ i : Fin M,μ.coeff (i.val+P+2))≤_
    rw [Fin.sum_univ_eq_sum_range (fun q => μ.coeff (q+P+2)) M]
    exact (summable_tailVariance μ P).sum_le_tsum (Finset.range M) (fun q _ => μ.nonneg _)
  have hmoment : (∑ i,(d i:ℝ)*c i)≤tailSlope μ P := by
    change (∑ i : Fin M,((i.val+P+2:ℕ):ℝ)*μ.coeff (i.val+P+2))≤_
    rw [Fin.sum_univ_eq_sum_range (fun q => ((q+P+2:ℕ):ℝ)*μ.coeff (q+P+2)) M]
    exact (summable_tailSlope μ P).sum_le_tsum (Finset.range M)
      (fun q _ => mul_nonneg (Nat.cast_nonneg _) (μ.nonneg _))
  let F := absoluteSupremum (fun x : UnitSphere N => feature d c x.val)
  have hLip := absoluteSupremum_lipschitz hN d c hc (tailVariance_nonneg μ P) hvar
  have he (J : Disorder N) : ‖tailSpherePartial μ P M J‖=F (finiteCoordinates p J) := by
    rw [tailSpherePartial,selectedSphereField_eq_tensorSphereField hN,tensorSphereField_norm hN]
  simp_rw [he]
  rw [(finiteCoordinates_hasLaw p hp).measure_eq (measurableSet_lt measurable_const hLip.continuous.measurable)]
  exact absoluteSupremum_upper_tail hN d c hc (fun i => by dsimp [d];omega)
    (tailSlope_nonneg μ P) (tailVariance_nonneg μ P) ht hmoment hvar

/-- Borell upper tail of the literal infinite series, obtained from its proved
uniform limit and finite Gaussian coefficient laws. -/
theorem tailSphere_upper_tail {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (P : ℕ) {t : ℝ} (ht : 0≤t) :
    disorderLaw N {J|2*N*Real.sqrt (tailSlope μ P)+t<‖tailSphere μ P J‖}≤
      ENNReal.ofReal (Real.exp (-t^2/(2*N*tailVariance μ P))) :=
  GaussianConcentrationLimit.strict_tail_bound_of_ae_tendsto
    (fun M J => ‖tailSpherePartial μ P M J‖) (fun J => ‖tailSphere μ P J‖)
    (fun M => (tailSpherePartial_continuous μ P M).norm.measurable)
    ((tailSpherePartial_tendsto_ae hN μ P).mono fun J hJ => hJ.norm) _ _
    (fun M => tailSpherePartial_upper_tail hN μ P M ht)

theorem tailSphere_eq_zero_of_variance_eq_zero {N : ℕ} (μ : InfiniteMixture)
    (P : ℕ) (hv : tailVariance μ P=0) (J : Disorder N) : tailSphere μ P J=0 := by
  have hc (q : ℕ) : μ.coeff (q+P+2)=0 := by
    have hh := (summable_tailVariance μ P).le_tsum q (fun j _ => μ.nonneg _)
    change _≤tailVariance μ P at hh
    rw [hv] at hh
    exact le_antisymm hh (μ.nonneg _)
  have hb (q : ℕ) : blockContinuous μ (q+P) J=0 := by
    ext x
    simp [blockContinuous,block,hc q]
  simp only [tailSphere,tailContinuous,hb,tsum_zero,map_zero]

/-- The source exponentially small truncation error, including its prescribed
zero-variance convention. The cutoff may depend on h, while the assertion is
uniform over all positive dimensions. -/
theorem tailSphere_small_probability_eventually (μ : InfiniteMixture) {h : ℝ} (hh : 0<h) :
    ∀ᶠ P in atTop,∀ N : ℕ,0<N →
      disorderLaw N {J|h*N<‖tailSphere μ P J‖}≤
        if tailVariance μ P=0 then 0 else
          ENNReal.ofReal (2*Real.exp (-h^2*N/(8*tailVariance μ P))) := by
  have ht : Tendsto (fun P => Real.sqrt (tailSlope μ P)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using Real.continuous_sqrt.continuousAt.tendsto.comp
      (tailSlope_tendsto_zero μ)
  filter_upwards [ht.eventually (Iio_mem_nhds (show (0:ℝ)<h/4 by positivity))] with P hP
  intro N hN
  have hNr : (0:ℝ)<N := Nat.cast_pos.mpr hN
  by_cases hv : tailVariance μ P=0
  · rw [if_pos hv]
    have he : {J : Disorder N|h*N<‖tailSphere μ P J‖}=∅ := by
      ext J
      simp only [tailSphere_eq_zero_of_variance_eq_zero μ P hv J,norm_zero,
        mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact not_lt.mpr (mul_nonneg hh.le hNr.le)
    rw [he,measure_empty]
  · rw [if_neg hv]
    have hthreshold : 2*N*Real.sqrt (tailSlope μ P)+h*N/2≤h*N := by
      have hm := mul_le_mul_of_nonneg_left hP.le (show (0:ℝ)≤2*N by positivity)
      nlinarith
    have hb := tailSphere_upper_tail hN μ P (t := h*N/2) (by positivity)
    have he : -(h*N/2)^2/(2*N*tailVariance μ P)= -h^2*N/(8*tailVariance μ P) := by
      field_simp
      ring
    rw [he] at hb
    apply (measure_mono (show {J : Disorder N|h*N<‖tailSphere μ P J‖}⊆
      {J|2*N*Real.sqrt (tailSlope μ P)+h*N/2<‖tailSphere μ P J‖}
      from fun J hJ => lt_of_le_of_lt hthreshold hJ)).trans
    exact hb.trans (ENNReal.ofReal_le_ofReal (by nlinarith [Real.exp_pos (-h^2*N/(8*tailVariance μ P))]))

end SlowEquilibration.SphericalInfiniteModel
