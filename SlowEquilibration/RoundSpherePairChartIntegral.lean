-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairCountGluing

/-! The genuine product round-area measure in the product chart. The
transported lower integral is valid even for nonmeasurable integrands. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RoundSpherePairChartIntegral
open MeasureTheory Set Function Metric
open SphericalModel SphereChartVolume SphericalChartKacRice SphericalKacRiceGluing
open SphericalPairChartGeometry SphericalPairCountGluing SphericalPairChartKacRice
open scoped ENNReal Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def chartWeight (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ENNReal.ofReal ((Real.sqrt (n+1:ℕ))^n*sphereChartWeightND u)

lemma chartWeight_measurable (n : ℕ) : Measurable (chartWeight n) :=
  (measurable_const.mul sphereChartWeightND_measurable).ennreal_ofReal

lemma chartWeight_eq_metric {n : ℕ} {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    chartWeight n u=ENNReal.ofReal (Real.sqrt (manuscriptChartGram n u).det) := by
  rw [manuscriptChart_riemannian_density hu]
  rfl

lemma round_map_chart (n : ℕ) (hn : 1 ≤ n) :
    manuscriptRoundVolume n=((volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) 2)).withDensity
      (chartWeight n)).map (manuscriptChart n) := by
  rw [← manuscriptRoundVolume_restrict_full_chart n hn,
    manuscriptRoundVolume_restrict_chart isOpen_ball.measurableSet (Subset.rfl)]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with u hu
  exact (chartWeight_eq_metric (by simpa using hu)).symm

def pairChartWeight (n : ℕ) (p : PairChart n) : ℝ≥0∞ := chartWeight n p.fst*chartWeight n p.snd

lemma pairChartWeight_measurable (n : ℕ) : Measurable (pairChartWeight n) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  exact ((chartWeight_measurable n).comp e.continuous.measurable.fst).mul
    ((chartWeight_measurable n).comp e.continuous.measurable.snd)

lemma pairChartMap_injOn (n : ℕ) : InjOn (pairChartMap n) (pairChartDomain n) := by
  intro p hp q hq he
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · exact SphericalKacRiceGluing.manuscriptChart_injOn n (by simpa using hp.1)
      (by simpa using hq.1) (congrArg Prod.fst he)
  · exact SphericalKacRiceGluing.manuscriptChart_injOn n (by simpa using hp.2)
      (by simpa using hq.2) (congrArg Prod.snd he)

lemma round_prod_map_chart (n : ℕ) (hn : 1 ≤ n) :
    (manuscriptRoundVolume n).prod (manuscriptRoundVolume n)=
      (((volume : Measure (PairChart n)).restrict (pairChartDomain n)).withDensity (pairChartWeight n)).map
        (pairChartMap n) := by
  let U := EuclideanSpace ℝ (Fin n)
  let ν : Measure U := volume.restrict (ball 0 2)
  have hdom : WithLp.ofLp ⁻¹' (ball (0 : U) 2 ×ˢ ball (0 : U) 2)=pairChartDomain n := by
    ext p
    simp only [mem_preimage,mem_prod,mem_ball,dist_zero_right]
    rfl
  have hmap : ((volume : Measure (PairChart n)).restrict (pairChartDomain n)).map WithLp.ofLp=ν.prod ν := by
    have h := ((WithLp.volume_preserving_ofLp U U).restrict_preimage (s := ball (0 : U) 2 ×ˢ ball (0 : U) 2)
      (isOpen_ball.measurableSet.prod isOpen_ball.measurableSet)).map_eq
    rw [hdom] at h
    simpa only [ν,Measure.prod_restrict,Measure.volume_eq_prod] using h
  have hweight := GaussianRegression.map_withDensity_equiv (MeasurableEquiv.toLp 2 (U×U)).symm
    ((volume : Measure (PairChart n)).restrict (pairChartDomain n)) (pairChartWeight n)
    (pairChartWeight_measurable n)
  change (((volume : Measure (PairChart n)).restrict (pairChartDomain n)).withDensity (pairChartWeight n)).map
    WithLp.ofLp=(((volume : Measure (PairChart n)).restrict (pairChartDomain n)).map WithLp.ofLp).withDensity (fun p => chartWeight n p.1*chartWeight n p.2) at hweight
  rw [hmap] at hweight
  rw [round_map_chart n hn,Measure.map_prod_map _ _
    (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable
    (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable,
    prod_withDensity (chartWeight_measurable n) (chartWeight_measurable n)]
  rw [← hweight,Measure.map_map
    ((RoundSphereChartIntegral.manuscriptChart_continuous n).measurable.prodMap
      (RoundSphereChartIntegral.manuscriptChart_continuous n).measurable)
    (WithLp.volume_preserving_ofLp U U).measurable]
  rfl

lemma lintegral_map_restrict_pair_chart (n : ℕ) (ν : Measure (PairChart n))
    (F : Vector (n+1) × Vector (n+1) → ℝ≥0∞) :
    (∫⁻ x,F x ∂(ν.restrict (pairChartDomain n)).map (pairChartMap n))=
      ∫⁻ p in pairChartDomain n,F (pairChartMap n p) ∂ν := by
  have hs := (pairChartDomain_isOpen n).measurableSet
  have he := (pairChartMap_continuous n).continuousOn.measurableEmbedding hs (pairChartMap_injOn n)
  have hm : (ν.restrict (pairChartDomain n)).map (pairChartMap n)=
      (ν.comap ((↑) : pairChartDomain n → PairChart n)).map
        ((pairChartDomain n).domRestrict (pairChartMap n)) := by
    rw [← map_comap_subtype_coe hs,
      Measure.map_map (pairChartMap_continuous n).measurable measurable_subtype_coe]
    rfl
  rw [hm,he.lintegral_map]
  exact lintegral_subtype_comap hs (fun p => F (pairChartMap n p))

/-- The independently constructed product round volume has the product
of the two actual chart Gram area densities, with no measurability premise
on the nonnegative varying-tangent-space integrand. -/
theorem round_prod_lintegral_chart (n : ℕ) (hn : 1 ≤ n)
    (F : Vector (n+1) × Vector (n+1) → ℝ≥0∞) :
    (∫⁻ x,F x ∂(manuscriptRoundVolume n).prod (manuscriptRoundVolume n))=
      ∫⁻ p in pairChartDomain n,
        (ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.fst).det)*
          ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.snd).det))*F (pairChartMap n p) := by
  rw [round_prod_map_chart n hn,← restrict_withDensity (pairChartDomain_isOpen n).measurableSet,
    lintegral_map_restrict_pair_chart,
    setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ (pairChartWeight_measurable n) _
      (pairChartDomain_isOpen n).measurableSet
      (Filter.Eventually.of_forall (fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top))]
  apply setLIntegral_congr_fun (pairChartDomain_isOpen n).measurableSet
  intro p hp
  dsimp only [Pi.mul_apply,pairChartWeight]
  rw [chartWeight_eq_metric hp.1,chartWeight_eq_metric hp.2]

theorem round_prod_overlap_lintegral_chart (n : ℕ) (hn : 1 ≤ n) (ρ : ℝ)
    (F : Vector (n+1) × Vector (n+1) → ℝ≥0∞) :
    (∫⁻ x in {x | |overlap x.1 x.2| < ρ},F x
      ∂(manuscriptRoundVolume n).prod (manuscriptRoundVolume n))=
      ∫⁻ p in pairOverlapDomain n ρ,
        (ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.fst).det)*
          ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.snd).det))*F (pairChartMap n p) := by
  classical
  let O : Set (Vector (n+1) × Vector (n+1)) := {x | |overlap x.1 x.2| < ρ}
  have hO : MeasurableSet O :=
    (isOpen_lt ((continuous_fst.inner continuous_snd).div_const _).abs continuous_const).measurableSet
  have hpre : MeasurableSet ((pairChartMap n) ⁻¹' O) := hO.preimage (pairChartMap_continuous n).measurable
  have h := round_prod_lintegral_chart n hn (O.indicator F)
  rw [lintegral_indicator hO] at h
  rw [h]
  have he : (fun p : PairChart n =>
      (ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.fst).det)*
        ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.snd).det))*O.indicator F (pairChartMap n p))=
      ((pairChartMap n) ⁻¹' O).indicator (fun p =>
        (ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.fst).det)*
          ENNReal.ofReal (Real.sqrt (manuscriptChartGram n p.snd).det))*F (pairChartMap n p)) := by
    funext p
    by_cases hp : pairChartMap n p ∈ O <;> simp [Set.indicator,hp]
  rw [he,setLIntegral_indicator hpre]
  congr 1
  congr 1
  exact inter_comm _ _

end SlowEquilibration.RoundSpherePairChartIntegral
