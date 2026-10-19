-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedPlantedBaseline
public import SlowEquilibration.ConstrainedConcentration

@[expose] public section

/-! # Actual expected weighted planted pressure at the unperturbed model

The literal deterministic planting and source penalty are bounded on the
actual sphere. Genuine Gaussian concentration therefore controls the
centered weighted pressure. Together with the independently proved closed
tails at F-J, this gives the mean contact without a thermodynamic formula
for perturbed transverse covariances.
-/
namespace SlowEquilibration.SphericalSourceWeightedPartition
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Metric
open SphericalModel SphericalBarycenter
open scoped Topology
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine integrability and sharp centered Gaussian concentration for
the literal planted and overlap-weighted source pressure. -/
theorem sourceWeightedPlantedPressure_integrable_concentration {N : ℕ}
    (hN : 1 ≤ N) (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β)
    (δ q₁ q₂ : ℝ) (x : Vector N) :
    Integrable (sourceWeightedPlantedPressure μ β δ q₁ q₂ x) (disorderLaw N μ.maxDegree) ∧
      ∀ ε : ℝ, 0 < ε → disorderLaw N μ.maxDegree
        {D | ε ≤ |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-
          (∫ E, sourceWeightedPlantedPressure μ β δ q₁ q₂ x E ∂disorderLaw N μ.maxDegree)|} ≤
        ENNReal.ofReal (2*Real.exp (-(ε^2*(N : ℝ))/(2*β^2*μ.xi 1))) := by
  let B : Set (Vector N) := {u | ‖u‖^2=(N : ℝ)}
  have hB : MeasurableSet B := (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet
  have hBae : ∀ᵐ u ∂sphereLaw N, u∈B := sphereLaw_support hN
  have hrestrict : (sphereLaw N).restrict B=sphereLaw N := Measure.restrict_eq_self_of_ae_mem hBae
  have hMass : 0 < (sphereLaw N) B := by
    have he := congrArg (fun ν : Measure (Vector N) => ν univ) hrestrict
    have hprob : (sphereLaw N) B=1 := by
      simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter,measure_univ] using he
    rw [hprob]
    norm_num
  let shift : Vector N → ℝ := fun u => β^2*(N : ℝ)*μ.xi (overlap u x)-
    2*(N : ℝ)*sourceProfile (plantedCoreCost μ β) δ q₁ q₂ (overlap u x)
  have hR : Continuous (fun u : Vector N => overlap u x) := by unfold overlap; fun_prop
  have hxi : Continuous μ.xi := continuous_iff_continuousAt.mpr (fun r => (μ.hasDerivAt_xi r).continuousAt)
  have hs : Continuous shift := ((hxi.comp hR).const_mul (β^2*(N : ℝ))).sub
    (((sourceProfile_contDiff (plantedCoreCost μ β) δ q₁ q₂).continuous.comp hR).const_mul (2*(N : ℝ)))
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).exists_bound_of_continuousOn
    hs.continuousOn
  have hBound : ∀ u∈B, |shift u| ≤ C := by
    intro u hu
    have hball : u∈closedBall (0 : Vector N) (Real.sqrt (N : ℝ)) := by
      change ‖u‖^2=(N : ℝ) at hu
      simp only [mem_closedBall,dist_zero_right]
      rw [← hu,Real.sqrt_sq (norm_nonneg u)]
    simpa only [Real.norm_eq_abs] using hC u hball
  obtain ⟨hInt,hConc⟩ := mixtureConstrainedLogPartition_concentration hN μ hβ B hB hMass
    shift hs.measurable C hBound
  have heq : sourceWeightedPlantedPressure μ β δ q₁ q₂ x=
      fun D => mixtureConstrainedLogPartition μ β B shift D/(N : ℝ) := by
    funext D
    unfold sourceWeightedPlantedPressure sourceWeightedPartition mixtureConstrainedLogPartition
    rw [hrestrict]
    congr 2
    apply integral_congr_ae
    exact .of_forall fun u => by
      have hfield := field_add_plantedShift hN (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) β x u D
      rw [covariancePolynomial_mixture] at hfield
      change Real.exp (β*field (mixtureCoefficients μ)
        (D+plantedShift (mixtureCoefficients μ) β x) u-2*(N : ℝ)*
          sourceProfile (plantedCoreCost μ β) δ q₁ q₂ (overlap u x))=
        Real.exp (β*field (mixtureCoefficients μ) D u+shift u)
      rw [hfield]
      congr 1
      dsimp only [shift]
      ring
  rw [heq]
  refine ⟨hInt.div_const _,?_⟩
  intro ε hε
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsets : {D : Disorder N μ.maxDegree | ε ≤ |mixtureConstrainedLogPartition μ β B shift D/(N : ℝ)-
        (∫ E, mixtureConstrainedLogPartition μ β B shift E/(N : ℝ) ∂disorderLaw N μ.maxDegree)|}=
      {D | ε*(N : ℝ) ≤ |mixtureConstrainedLogPartition μ β B shift D-
        (∫ E, mixtureConstrainedLogPartition μ β B shift E ∂disorderLaw N μ.maxDegree)|} := by
    ext D
    change (ε ≤ |mixtureConstrainedLogPartition μ β B shift D/(N : ℝ)-
      (∫ E, mixtureConstrainedLogPartition μ β B shift E/(N : ℝ) ∂disorderLaw N μ.maxDegree)|) ↔ _
    rw [integral_div,← sub_div,abs_div,abs_of_pos hNr]
    exact le_div_iff₀ hNr
  rw [hsets]
  exact hConc ε hε

/-- Exact normalization matching the source definition of its expected
finite-volume amplitude pressure. -/
theorem sourceWeightedPlantedMean_eq_logIntegral {N : ℕ} (μ : FiniteMixture)
    (β δ q₁ q₂ : ℝ) (x : Vector N) :
    (∫ D, sourceWeightedPlantedPressure μ β δ q₁ q₂ x D ∂disorderLaw N μ.maxDegree)=
      (∫ D, Real.log (sourceWeightedPartition β
        (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
        (plantedCoreCost μ β) δ q₁ q₂ x) ∂disorderLaw N μ.maxDegree)/(N : ℝ) := by
  change (∫ D, Real.log (sourceWeightedPartition β
    (fieldOfMixture μ (D+plantedShift (mixtureCoefficients μ) β x))
    (plantedCoreCost μ β) δ q₁ q₂ x)/(N : ℝ) ∂disorderLaw N μ.maxDegree)=_
  rw [integral_div]

private theorem exp_decay {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℕ => Real.exp (-a*(N : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_natCast_atTop_atTop.const_mul_atTop ha) using 1
  ext N
  simp only [Function.comp_apply,neg_mul]

/-- The actual expected normalized weighted planted pressure approaches
F-J uniformly in the reference. Closed tails and Gaussian concentration
are both proved providers, not hypotheses of this theorem. -/
theorem convex_sourceWeightedPlantedMean_eventually_close (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ q₁ q₂ ε : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 ≤ δ)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (x : Vector N), ‖x‖^2=(N : ℝ) →
      |(∫ D, sourceWeightedPlantedPressure μ β δ q₁ q₂ x D ∂disorderLaw N μ.maxDegree)-
        (β^2*μ.xi 1/2-plantedCoreCost μ β)| < ε := by
  let s := ε/2
  have hs : 0 < s := by dsimp only [s]; positivity
  have hβpos : 0 < β := μ.dynamicalThreshold_pos.trans hβ
  have hξ : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  let c := s^2/(2*β^2*μ.xi 1)
  have hcpos : 0 < c := by dsimp only [c]; positivity
  obtain ⟨γ,hγ,hTail⟩ := convex_sourceWeightedPlantedPressure_closed_tail μ hconv
    hβ hβs hδ hc hs
  have hsum : Tendsto (fun N : ℕ => 8*Real.exp (-γ*(N : ℝ))+2*Real.exp (-c*(N : ℝ)))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,add_zero] using ((exp_decay hγ).const_mul 8).add ((exp_decay hcpos).const_mul 2)
  filter_upwards [hTail,hsum.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)),
    eventually_ge_atTop (1 : ℕ)] with N hTailN hSmall hN
  intro x hx
  let d := disorderLaw N μ.maxDegree
  let f := sourceWeightedPlantedPressure μ β δ q₁ q₂ x
  let m := ∫ D, f D ∂d
  let L := β^2*μ.xi 1/2-plantedCoreCost μ β
  let E₀ : Set (Disorder N μ.maxDegree) := {D | s ≤ |f D-L|}
  let E₁ : Set (Disorder N μ.maxDegree) := {D | s ≤ |f D-m|}
  have ht : d.real E₀ ≤ 8*Real.exp (-γ*(N : ℝ)) := by
    change (disorderLaw N μ.maxDegree).real {D | s ≤
      |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-(β^2*μ.xi 1/2-plantedCoreCost μ β)|} ≤ _
    have hb := ENNReal.toReal_mono (by finiteness) (hTailN x hx)
    simpa only [Measure.real,ENNReal.toReal_mul,ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (Real.exp_nonneg _)] using hb
  have hcon := (sourceWeightedPlantedPressure_integrable_concentration hN μ hβpos δ q₁ q₂ x).2 s hs
  have he : -(s^2*(N : ℝ))/(2*β^2*μ.xi 1)=-c*(N : ℝ) := by dsimp only [c]; ring
  rw [he] at hcon
  have hct : d.real E₁ ≤ 2*Real.exp (-c*(N : ℝ)) := by
    change (disorderLaw N μ.maxDegree).real {D | s ≤
      |sourceWeightedPlantedPressure μ β δ q₁ q₂ x D-
        (∫ E, sourceWeightedPlantedPressure μ β δ q₁ q₂ x E ∂disorderLaw N μ.maxDegree)|} ≤ _
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcon
    simpa only [Measure.real,ENNReal.toReal_ofReal (show 0 ≤ 2*Real.exp (-c*(N : ℝ)) by positivity)] using hb
  change |m-L| < ε
  by_contra hbad
  have hbad' : ε ≤ |m-L| := le_of_not_gt hbad
  have hcover : (univ : Set (Disorder N μ.maxDegree)) ⊆ E₀ ∪ E₁ := by
    intro D _
    by_contra hD
    have hnot₀ : D∉E₀ := fun h => hD (Or.inl h)
    have hnot₁ : D∉E₁ := fun h => hD (Or.inr h)
    have h₀ : |f D-L| < s := lt_of_not_ge hnot₀
    have h₁ : |f D-m| < s := lt_of_not_ge hnot₁
    have htriangle : |m-L| ≤ |f D-m|+|f D-L| := by
      have h := abs_sub (m-f D) (L-f D)
      rw [show (m-f D)-(L-f D)=m-L by ring,abs_sub_comm m (f D),abs_sub_comm L (f D)] at h
      exact h
    dsimp only [s] at h₀ h₁
    linarith
  have hprob := (measureReal_mono (μ := d) hcover).trans (measureReal_union_le (μ := d) E₀ E₁)
  have huniv : d.real univ=1 := probReal_univ
  rw [huniv] at hprob
  linarith

/-- Exact center contact for any genuine sequence of spherical references,
on the original Gaussian disorder. -/
theorem convex_sourceWeightedPlantedExpectedPressure_tendsto (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β δ q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hδ : 0 ≤ δ)
    (hc : IsAdmissibleCollar μ β q₁ q₂) (x : ∀ N : ℕ, Vector N)
    (hx : ∀ N, ‖x N‖^2=(N : ℝ)) :
    Tendsto (fun N => ∫ D, sourceWeightedPlantedPressure μ β δ q₁ q₂ (x N) D
      ∂disorderLaw N μ.maxDegree) atTop (𝓝 (β^2*μ.xi 1/2-plantedCoreCost μ β)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [convex_sourceWeightedPlantedMean_eventually_close μ hconv hβ hβs hδ hc hε]
    with N hN
  simpa only [Real.dist_eq] using hN (x N) (hx N)

end
end SlowEquilibration.SphericalSourceWeightedPartition
