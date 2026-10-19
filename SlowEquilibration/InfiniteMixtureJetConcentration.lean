-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureTensorJetConcentration
public import SlowEquilibration.SphericalInfiniteFiniteCoordinates
public import SlowEquilibration.SphericalInfiniteJetSeries
public import SlowEquilibration.GaussianConcentrationLimit

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal
open PureTensorJetBounds PureTensorJetConcentration
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- One source-dependent mean constant controls all three low jets. -/
def jetMeanConstant (μ : InfiniteMixture) : ℝ :=
  8 * ∑' p : ℕ, ((p+2 : ℕ) : ℝ)^(5/2 : ℝ) * Real.sqrt (μ.coeff (p+2))

/-- A positive variance proxy, uniform in the truncation and the dimension. -/
def jetVarianceConstant (μ : InfiniteMixture) : ℝ :=
  1 + ∑' p : ℕ, ((p+2 : ℕ) : ℝ)^4 * μ.coeff (p+2)

def jetScale (N j : ℕ) : ℝ := (N : ℝ)^(1-(j : ℝ)/2)
def jetLipschitzScale (N j : ℕ) : ℝ := (N : ℝ)^((1-(j : ℝ))/2)

def partialJetEnvelope {N : ℕ} (μ : InfiniteMixture) (j n : ℕ) (J : Disorder N) : ℝ :=
  ∑ i : Fin n, blockJetEnvelope μ j i.val J

def fullJetEnvelope {N : ℕ} (μ : InfiniteMixture) (j : ℕ) (J : Disorder N) : ℝ :=
  ∑' p,blockJetEnvelope μ j p J

theorem jetMeanConstant_nonneg (μ : InfiniteMixture) : 0 ≤ jetMeanConstant μ := by
  exact mul_nonneg (by norm_num) (tsum_nonneg (fun p => by positivity))

theorem jetVarianceConstant_pos (μ : InfiniteMixture) : 0 < jetVarianceConstant μ := by
  have hh : 0 ≤ ∑' p : ℕ, ((p+2 : ℕ) : ℝ)^4 * μ.coeff (p+2) :=
    tsum_nonneg (fun p => mul_nonneg (by positivity) (μ.nonneg _))
  dsimp [jetVarianceConstant]
  linarith

theorem jetScale_pos {N : ℕ} (hN : 0 < N) (j : ℕ) : 0 < jetScale N j :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _

theorem partialJetEnvelope_measurable {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture) (j n : ℕ) :
    Measurable (partialJetEnvelope (N := N) μ j n) := by
  exact Finset.measurable_fun_sum _ (fun i _ => (blockJetEnvelope_continuous hN μ j i.val).measurable)

theorem partialJetEnvelope_integrable {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture) (j n : ℕ) :
    Integrable (partialJetEnvelope (N := N) μ j n) (disorderLaw N) :=
  integrable_finset_sum _ (fun i _ => blockJetEnvelope_integrable hN μ j i.val)

theorem blockJetEnvelope_mean_le_scale {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (j p : ℕ) (hj : j ≤ 2) :
    (∫ J,blockJetEnvelope μ j p J ∂disorderLaw N) ≤
      8 * (((p+2 : ℕ) : ℝ)^(5/2 : ℝ) * Real.sqrt (μ.coeff (p+2))) * jetScale N j := by
  unfold blockJetEnvelope
  rw [integral_const_mul]
  have he := (degree_hasLaw (N := N) p).integral_comp
    (pureJetEnvelope_integrable (p := p+2) (j := j) hN).aestronglyMeasurable
  dsimp only [Function.comp_def] at he
  rw [he]
  have hh := mul_le_mul_of_nonneg_left
    (expected_pureJetEnvelope_le_eight (p := p+2) (j := j) hN (by omega) hj)
    (Real.sqrt_nonneg (μ.coeff (p+2)))
  have hp : ((p+2 : ℕ) : ℝ)^j ≤ ((p+2 : ℕ) : ℝ)^2 :=
    pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p+2)) hj
  have hp' : ((p+2 : ℕ) : ℝ)^2 * Real.sqrt (p+2 : ℕ) = ((p+2 : ℕ) : ℝ)^(5/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_add (by positivity)]
    congr 1
    norm_num
  calc
    _ ≤ Real.sqrt (μ.coeff (p+2)) * (8 * ((p+2 : ℕ) : ℝ)^j * Real.sqrt (p+2 : ℕ) * jetScale N j) := hh
    _ ≤ Real.sqrt (μ.coeff (p+2)) * (8 * ((p+2 : ℕ) : ℝ)^2 * Real.sqrt (p+2 : ℕ) * jetScale N j) := by
      gcongr
      exact (jetScale_pos hN j).le
    _ = _ := by
      rw [show 8 * ((p+2 : ℕ) : ℝ)^2 * Real.sqrt (p+2 : ℕ) * jetScale N j =
        8 * (((p+2 : ℕ) : ℝ)^2 * Real.sqrt (p+2 : ℕ)) * jetScale N j by ring,hp']
      ring

theorem partialJetEnvelope_mean_le {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (j n : ℕ) (hj : j ≤ 2) :
    (∫ J,partialJetEnvelope μ j n J ∂disorderLaw N) ≤ jetMeanConstant μ * jetScale N j := by
  unfold partialJetEnvelope
  rw [integral_finset_sum _ (fun i _ => blockJetEnvelope_integrable hN μ j i.val)]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    blockJetEnvelope_mean_le_scale hN μ j i.val hj)
  apply hh.trans
  rw [← Finset.sum_mul,← Finset.mul_sum,Fin.sum_univ_eq_sum_range
    (fun p : ℕ => ((p+2 : ℕ) : ℝ)^(5/2 : ℝ) * Real.sqrt (μ.coeff (p+2))) n]
  apply mul_le_mul_of_nonneg_right _ (jetScale_pos hN j).le
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 8)
  exact (μ.summable_shifted_weighted_sqrt (s := 5/2) le_rfl).sum_le_tsum _
    (fun p _ => by positivity)

theorem finite_jet_variance_le (μ : InfiniteMixture) (j n : ℕ) (hj : j ≤ 2) :
    (∑ i : Fin n,(Real.sqrt (μ.coeff (i.val+2))*((i.val+2 : ℕ) : ℝ)^j)^2) ≤ jetVarianceConstant μ := by
  have hp (p : ℕ) : (Real.sqrt (μ.coeff (p+2))*((p+2 : ℕ) : ℝ)^j)^2 ≤
      ((p+2 : ℕ) : ℝ)^4 * μ.coeff (p+2) := by
    rw [mul_pow,Real.sq_sqrt (μ.nonneg _),← pow_mul]
    calc
      _ ≤ μ.coeff (p+2) * ((p+2 : ℕ) : ℝ)^4 := by
        apply mul_le_mul_of_nonneg_left _ (μ.nonneg _)
        exact pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ p+2)) (by omega)
      _ = _ := mul_comm _ _
  have hs := (summable_nat_add_iff 2).2 (μ.summable_moment (k := 4) (by omega))
  calc
    _ ≤ ∑ i : Fin n,((i.val+2 : ℕ) : ℝ)^4 * μ.coeff (i.val+2) := Finset.sum_le_sum (fun i _ => hp i.val)
    _ ≤ ∑' p : ℕ,((p+2 : ℕ) : ℝ)^4 * μ.coeff (p+2) := by
      rw [Fin.sum_univ_eq_sum_range (fun p : ℕ => ((p+2 : ℕ) : ℝ)^4 * μ.coeff (p+2)) n]
      exact hs.sum_le_tsum _ (fun p _ => mul_nonneg (by positivity) (μ.nonneg _))
    _ ≤ _ := by dsimp [jetVarianceConstant]; linarith

private theorem partialJetEnvelope_coordinates {N : ℕ} (μ : InfiniteMixture) (j n : ℕ) (J : Disorder N) :
    partialJetEnvelope μ j n J =
      weightedEnvelope (fun i : Fin n => i.val+2) (fun i => Real.sqrt (μ.coeff (i.val+2))) j
        (finiteCoordinates (fun i : Fin n => i.val) J) := by
  apply Finset.sum_congr rfl
  intro i _
  rfl

private theorem partialEnvelope_lipschitz {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (j n : ℕ) (hj : j ≤ 2) :
    LipschitzWith (jetLipschitzScale N j * Real.sqrt (jetVarianceConstant μ)).toNNReal
      (weightedEnvelope (N := N) (fun i : Fin n => i.val+2)
        (fun i => Real.sqrt (μ.coeff (i.val+2))) j) := by
  have hh := weightedEnvelope_lipschitz hN (fun i : Fin n => i.val+2)
    (fun i => Real.sqrt (μ.coeff (i.val+2))) (fun _ => Real.sqrt_nonneg _)
    (fun _ => by omega) (fun _ => by omega : ∀ i : Fin n,j ≤ i.val+2)
  apply hh.weaken
  apply Real.toNNReal_le_toNNReal
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  exact Real.sqrt_le_sqrt (finite_jet_variance_le μ j n hj)

private theorem jet_concentration_exponent {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture) (j : ℕ) :
    -(jetScale N j)^2 / (2*(jetLipschitzScale N j * Real.sqrt (jetVarianceConstant μ))^2) =
      -(N : ℝ)/(2*jetVarianceConstant μ) := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hv := jetVarianceConstant_pos μ
  have hD : jetLipschitzScale N j ≠ 0 := (Real.rpow_pos_of_pos hN' _).ne'
  have he : jetScale N j = Real.sqrt N * jetLipschitzScale N j := by
    rw [jetScale,jetLipschitzScale,Real.sqrt_eq_rpow,← Real.rpow_add hN']
    congr 1
    ring
  rw [he,mul_pow,mul_pow,Real.sq_sqrt hN'.le,Real.sq_sqrt hv.le]
  field_simp [hD,hv.ne']

/-- Uniform finite tails on the full original countable disorder law. -/
theorem partialJetEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (j n : ℕ) (hj : j ≤ 2) :
    disorderLaw N {J | (jetMeanConstant μ+1)*jetScale N j < partialJetEnvelope μ j n J} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ)/(2*jetVarianceConstant μ))) := by
  let F := weightedEnvelope (N := N) (fun i : Fin n => i.val+2)
    (fun i => Real.sqrt (μ.coeff (i.val+2))) j
  let P := SYK.standardGaussianMeasureOnEuclidean (SelectedCoordinate N (fun i : Fin n => i.val))
  have hF := partialEnvelope_lipschitz hN μ j n hj
  have hLaw := finiteCoordinates_hasLaw (N := N) (fun i : Fin n => i.val) Fin.val_injective
  have hmean : (∫ g,F g ∂P) = ∫ J,partialJetEnvelope μ j n J ∂disorderLaw N := by
    have hh := hLaw.integral_comp hF.continuous.aestronglyMeasurable
    simpa only [Function.comp_def,← partialJetEnvelope_coordinates] using hh.symm
  have ht := GaussianNormConcentration.centered_lipschitz_upper_tail F
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _) (Real.sqrt_nonneg _)) hF (jetScale_pos hN j).le
  change P.real {g | (∫ z,F z ∂P)+jetScale N j ≤ F g} ≤
    Real.exp (-(jetScale N j)^2 / (2*(jetLipschitzScale N j * Real.sqrt (jetVarianceConstant μ))^2)) at ht
  rw [jet_concentration_exponent hN μ j] at ht
  have hmap := hLaw.measureReal_eq (p := fun g => (∫ z,F z ∂P)+jetScale N j ≤ F g)
    (measurableSet_le measurable_const hF.continuous.measurable)
  have hb : (disorderLaw N).real {J | (jetMeanConstant μ+1)*jetScale N j < partialJetEnvelope μ j n J} ≤
      Real.exp (-(N : ℝ)/(2*jetVarianceConstant μ)) := by
    calc
      _ ≤ (disorderLaw N).real {J | (∫ g,F g ∂P)+jetScale N j ≤ F (finiteCoordinates (fun i : Fin n => i.val) J)} := by
        apply measureReal_mono ?_ (measure_ne_top _ _)
        intro J hJ
        change (∫ g,F g ∂P)+jetScale N j ≤ F (finiteCoordinates (fun i : Fin n => i.val) J)
        rw [show F (finiteCoordinates (fun i : Fin n => i.val) J) = partialJetEnvelope μ j n J from
          (partialJetEnvelope_coordinates μ j n J).symm,hmean]
        have hm := partialJetEnvelope_mean_le hN μ j n hj
        change (jetMeanConstant μ+1)*jetScale N j < partialJetEnvelope μ j n J at hJ
        linarith
      _ = P.real {g | (∫ z,F z ∂P)+jetScale N j ≤ F g} := hmap
      _ ≤ _ := ht
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
  exact hb

/-- A genuine Gaussian exponential bound for each complete infinite jet envelope. -/
theorem fullJetEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (j : ℕ) (hj : j ≤ 2) :
    disorderLaw N {J | (jetMeanConstant μ+1)*jetScale N j < fullJetEnvelope μ j J} ≤
      ENNReal.ofReal (Real.exp (-(N : ℝ)/(2*jetVarianceConstant μ))) := by
  apply GaussianConcentrationLimit.strict_tail_bound_of_ae_tendsto
    (fun n => partialJetEnvelope μ j n) (fullJetEnvelope μ j)
    (fun n => partialJetEnvelope_measurable hN μ j n) ?_
    _ _ (fun n => partialJetEnvelope_upper_tail hN μ j n hj)
  filter_upwards [blockJetEnvelope_summable_ae hN μ j hj] with J hJ
  have he (n : ℕ) : partialJetEnvelope μ j n J = ∑ p ∈ Finset.range n,blockJetEnvelope μ j p J :=
    Fin.sum_univ_eq_sum_range (fun p : ℕ => blockJetEnvelope μ j p J) n
  simp_rw [he]
  exact hJ.hasSum.tendsto_sum_nat

/-- The infinite envelope is a measurable function of the original tensor disorder. -/
theorem fullJetEnvelope_measurable {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture) (j : ℕ) :
    Measurable (fullJetEnvelope (N := N) μ j) := by
  exact Measurable.tsum (fun p => (blockJetEnvelope_continuous hN μ j p).measurable)

/-- All three source jet scales hold simultaneously, with exponential failure probability. -/
theorem threeJetEnvelope_upper_tail {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture) :
    disorderLaw N {J | ∃ j : Fin 3,
      (jetMeanConstant μ+1)*jetScale N j.val < fullJetEnvelope μ j.val J} ≤
      ENNReal.ofReal (3 * Real.exp (-(N : ℝ)/(2*jetVarianceConstant μ))) := by
  have he : {J : Disorder N | ∃ j : Fin 3,
      (jetMeanConstant μ+1)*jetScale N j.val < fullJetEnvelope μ j.val J} =
      ⋃ j : Fin 3,{J | (jetMeanConstant μ+1)*jetScale N j.val < fullJetEnvelope μ j.val J} := by
    ext J
    simp only [mem_setOf_eq,mem_iUnion]
  rw [he]
  calc
    _ ≤ ∑' j : Fin 3,disorderLaw N {J | (jetMeanConstant μ+1)*jetScale N j.val < fullJetEnvelope μ j.val J} :=
      measure_iUnion_le _
    _ ≤ ∑' _j : Fin 3,ENNReal.ofReal (Real.exp (-(N : ℝ)/(2*jetVarianceConstant μ))) :=
      ENNReal.tsum_le_tsum (fun j => fullJetEnvelope_upper_tail hN μ j.val (by omega))
    _ = _ := by simp [ENNReal.ofReal_mul]

/-- The proved envelope bounds the actual uniformly convergent tensor-jet series. -/
theorem jetSeries_norm_le_fullJetEnvelope {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ) (j : ℕ) (hj : j ≤ 2)
    (x : SphericalModel.Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    ‖∑' p,iteratedFDeriv ℝ j (block μ p J) x‖ ≤ fullJetEnvelope μ j J := by
  have hb (p : ℕ) := block_iteratedFDeriv_norm_le hN μ j p J x hx
  have hs : Summable (fun p => ‖iteratedFDeriv ℝ j (block μ p J) x‖) :=
    (hJ j hj).of_nonneg_of_le (fun p => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb (hJ j hj))

/-- The same envelope controls the literal scalar field on the full closed ball. -/
theorem field_norm_le_fullJetEnvelope {N : ℕ} (hN : 0 < N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J ∈ summableJetDisorder μ)
    (x : SphericalModel.Vector N) (hx : ‖x‖ ≤ Real.sqrt N) :
    ‖field μ J x‖ ≤ fullJetEnvelope μ 0 J := by
  have hb (p : ℕ) : ‖block μ p J x‖ ≤ blockJetEnvelope μ 0 p J := by
    simpa only [norm_iteratedFDeriv_zero] using block_iteratedFDeriv_norm_le hN μ 0 p J x hx
  have hs : Summable (fun p => ‖block μ p J x‖) :=
    (hJ 0 (by omega)).of_nonneg_of_le (fun p => norm_nonneg _) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb (hJ 0 (by omega)))

theorem jetScale_zero (N : ℕ) : jetScale N 0 = N := by simp [jetScale]
theorem jetScale_one (N : ℕ) : jetScale N 1 = Real.sqrt N := by
  simp only [jetScale,Nat.cast_one,Real.sqrt_eq_rpow]
  congr 1
  norm_num
theorem jetScale_two (N : ℕ) : jetScale N 2 = 1 := by norm_num [jetScale]

/-- Dimension-independent constants for the source exponential three-jet event. -/
theorem exists_threeJetEnvelope_constants (μ : InfiniteMixture) :
    ∃ K c : ℝ,0 < K ∧ 0 < c ∧ ∀ N : ℕ,0 < N →
      disorderLaw N {J | ∃ j : Fin 3,K*jetScale N j.val < fullJetEnvelope μ j.val J} ≤
        ENNReal.ofReal (4 * Real.exp (-c*N)) := by
  refine ⟨jetMeanConstant μ+1,1/(2*jetVarianceConstant μ),by linarith [jetMeanConstant_nonneg μ],
    div_pos (by norm_num) (mul_pos (by norm_num) (jetVarianceConstant_pos μ)),?_⟩
  intro N hN
  apply (threeJetEnvelope_upper_tail hN μ).trans
  apply ENNReal.ofReal_le_ofReal
  have he : -(N : ℝ)/(2*jetVarianceConstant μ) = -(1/(2*jetVarianceConstant μ))*N := by ring
  rw [he]
  nlinarith [Real.exp_pos (-(1/(2*jetVarianceConstant μ))*N)]

end SlowEquilibration.SphericalInfiniteModel
