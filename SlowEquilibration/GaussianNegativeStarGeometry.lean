-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! The geometric step in Panchenko's positivity principle,
arXiv:0708.2453v1, equations (2.7)--(2.8). All probabilities are under
ordinary Hilbert-space laws. The nonnegative mean Gram is derived by
Bochner Fubini, with no overlap positivity assumption. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianNegativeStarGeometry

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal InnerProductSpace BigOperators

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]

/-- Actual negative-overlap neighbors of one point. -/
def negativeNeighbors (ε : ℝ) (z : H) : Set H := {y | inner ℝ z y ≤ -ε}

/-- Actual conditional negative-neighbor probability. -/
def negativeNeighborMass (ν : Measure H) (ε : ℝ) (z : H) : ℝ :=
  ν.real (negativeNeighbors ε z)

omit [CompleteSpace H] [SecondCountableTopology H] in
theorem negativeNeighbors_measurable (ε : ℝ) (z : H) :
    MeasurableSet (negativeNeighbors ε z) :=
  measurableSet_le (continuous_const.inner continuous_id).measurable measurable_const

omit [CompleteSpace H] in
theorem negativeNeighborMass_measurable (ν : Measure H) [IsProbabilityMeasure ν] (ε : ℝ) :
    Measurable (negativeNeighborMass ν ε) := by
  have hB : MeasurableSet {p : H × H | inner ℝ p.1 p.2 ≤ -ε} :=
    measurableSet_le (continuous_fst.inner continuous_snd).measurable measurable_const
  exact (Kernel.measurable_kernel_prodMk_left (κ := Kernel.const H ν) hB).ennreal_toReal

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
theorem negativeNeighborMass_nonneg (ν : Measure H) (ε : ℝ) (z : H) :
    0 ≤ negativeNeighborMass ν ε z := measureReal_nonneg

omit [CompleteSpace H] [SecondCountableTopology H] [BorelSpace H] in
theorem negativeNeighborMass_le_one (ν : Measure H) [IsProbabilityMeasure ν] (ε : ℝ) (z : H) :
    negativeNeighborMass ν ε z ≤ 1 := measureReal_le_one

/-- Points having at least γ negative-neighbor mass. -/
def badCenters (ν : Measure H) (ε γ : ℝ) : Set H :=
  {z | γ ≤ negativeNeighborMass ν ε z}

omit [CompleteSpace H] in
theorem badCenters_measurable (ν : Measure H) [IsProbabilityMeasure ν] (ε γ : ℝ) :
    MeasurableSet (badCenters ν ε γ) :=
  measurableSet_le measurable_const (negativeNeighborMass_measurable ν ε)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
private theorem integrable_id_unit (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) : Integrable (fun z : H => z) ν :=
  Integrable.of_bound measurable_id.aestronglyMeasurable 1 hν

omit [CompleteSpace H] [SecondCountableTopology H] in
private theorem integrable_inner_unit (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (z : H) : Integrable (fun y => inner ℝ z y) ν := by
  apply Integrable.of_bound (continuous_const.inner continuous_id).measurable.aestronglyMeasurable ‖z‖
  filter_upwards [hν] with y hy
  exact (norm_inner_le_norm z y).trans (by nlinarith [norm_nonneg z])

/-- Actual restricted mean Gram is the squared norm of its Bochner mean. -/
theorem restricted_gram_eq_norm_sq (ν : Measure H) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) (U : Set H) :
    (∫ p : H × H, inner ℝ p.1 p.2 ∂(ν.restrict U).prod (ν.restrict U)) =
      ‖∫ z, z ∂ν.restrict U‖^2 := by
  have hi := (integrable_id_unit ν hν).restrict (s := U)
  have he := integral_prod_bilin (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) hi hi
  change (∫ p : H × H, inner ℝ p.1 p.2 ∂(ν.restrict U).prod (ν.restrict U)) =
    inner ℝ (∫ z, z ∂ν.restrict U) (∫ z, z ∂ν.restrict U) at he
  simpa only [real_inner_self_eq_norm_sq] using he

omit [CompleteSpace H] [SecondCountableTopology H] in
private theorem inner_row_bound (ν : Measure H) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) {ε γ : ℝ} (hε : 0 < ε)
    (z : H) (hz : ‖z‖ ≤ 1) (hbad : γ ≤ negativeNeighborMass ν ε z)
    (U : Set H) :
    (∫ y, inner ℝ z y ∂ν.restrict U) ≤
      -ε*ν.real U+(1+ε)*(1-γ) := by
  let A := negativeNeighbors ε z
  have hA : MeasurableSet A := negativeNeighbors_measurable ε z
  have hr : ∀ᵐ y ∂ν.restrict U, ‖y‖ ≤ 1 := ae_restrict_of_ae hν
  have hi := integrable_inner_unit (ν.restrict U) hr z
  have hI : Integrable (Aᶜ.indicator (fun _ : H => (1:ℝ))) (ν.restrict U) :=
    (integrable_const 1).indicator hA.compl
  have hupper := integral_mono_ae hi ((integrable_const (-ε)).add (hI.const_mul (1+ε))) (by
    filter_upwards [hr] with y hy
    change inner ℝ z y ≤ -ε+(1+ε)*Aᶜ.indicator (fun _ : H => (1:ℝ)) y
    by_cases hya : y ∈ A
    · rw [indicator_of_notMem (show y ∉ Aᶜ from notMem_compl_iff.mpr hya)]
      change inner ℝ z y ≤ -ε at hya
      simpa only [mul_zero, add_zero] using hya
    · rw [indicator_of_mem (show y ∈ Aᶜ from hya), mul_one]
      have hb := (real_inner_le_norm z y).trans (by nlinarith [norm_nonneg z, norm_nonneg y])
      linarith)
  have hmass : (ν.restrict U).real Aᶜ ≤ 1-γ := by
    have hm : (ν.restrict U).real Aᶜ ≤ ν.real Aᶜ :=
      ENNReal.toReal_mono (measure_ne_top ν Aᶜ) (Measure.restrict_le_self Aᶜ)
    have hc : ν.real Aᶜ=1-ν.real A := by rw [measureReal_compl hA, probReal_univ]
    rw [hc] at hm
    change γ ≤ ν.real A at hbad
    linarith
  change (∫ y, inner ℝ z y ∂ν.restrict U) ≤
    (∫ y, -ε+(1+ε)*Aᶜ.indicator (fun _ : H => (1:ℝ)) y ∂ν.restrict U) at hupper
  rw [integral_add (integrable_const (-ε)) (hI.const_mul (1+ε)), integral_const_mul,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul,
    integral_indicator_const 1 hA.compl, smul_eq_mul, mul_one] at hupper
  calc
    _ ≤ ν.real U*(-ε)+(1+ε)*(ν.restrict U).real Aᶜ := hupper
    _ ≤ -ε*ν.real U+(1+ε)*(1-γ) := by nlinarith

/-- The actual Hilbert geometry bounds the mass of points whose
negative-neighbor probability is at least γ. -/
theorem badCenters_mass_le (ν : Measure H) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (_hγ : 0 < γ) (hγ1 : γ < 1) :
    ν.real (badCenters ν ε γ) ≤ 2*(1-γ)/ε := by
  let U := badCenters ν ε γ
  have hU := badCenters_measurable ν ε γ
  have hr : ∀ᵐ z ∂ν.restrict U, ‖z‖ ≤ 1 := ae_restrict_of_ae hν
  have hi := integrable_id_unit (ν.restrict U) hr
  have hip : Integrable (fun p : H × H => inner ℝ p.1 p.2)
      ((ν.restrict U).prod (ν.restrict U)) :=
    hi.op_fst_snd (by fun_prop) ⟨‖innerSL ℝ‖, (innerSL ℝ).le_opNorm₂⟩ hi
  have hupper := integral_mono_ae hip.integral_prod_left
    (integrable_const (-ε*ν.real U+(1+ε)*(1-γ))) (by
      filter_upwards [hr, ae_restrict_mem hU] with z hz hzU
      exact inner_row_bound ν hν hε z hz hzU U)
  rw [← integral_prod _ hip, restricted_gram_eq_norm_sq ν hν U,
    integral_const, measureReal_restrict_apply_univ, smul_eq_mul] at hupper
  have hp : 0 ≤ ν.real U := measureReal_nonneg
  by_cases hp0 : ν.real U=0
  · rw [show ν.real (badCenters ν ε γ)=0 from hp0]
    positivity
  · have hpp : 0 < ν.real U := lt_of_le_of_ne hp (Ne.symm hp0)
    have hprod : 0 ≤ ν.real U*(-ε*ν.real U+(1+ε)*(1-γ)) :=
      (sq_nonneg _).trans hupper
    have hbound : ε*ν.real U ≤ (1+ε)*(1-γ) := by
      have hnon := nonneg_of_mul_nonneg_right hprod hpp
      linarith
    apply (le_div_iff₀ hε).mpr
    change ν.real U*ε ≤ 2*(1-γ)
    nlinarith

/-- The actual negative star under n+1 independent samples. -/
def negativeStar (ε : ℝ) (n : ℕ) : Set (Fin (n+1) → H) :=
  {σ | ∀ j : Fin n, inner ℝ (σ 0) (σ j.succ) ≤ -ε}

private def conditionalStar (ε : ℝ) (n : ℕ) : Set (H × (Fin n → H)) :=
  {p | ∀ j : Fin n, inner ℝ p.1 (p.2 j) ≤ -ε}

omit [CompleteSpace H] in
theorem negativeStar_measurable (ε : ℝ) (n : ℕ) :
    MeasurableSet (negativeStar (H := H) ε n) := by
  rw [negativeStar, ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le
    ((continuous_apply 0).inner (continuous_apply j.succ)).measurable measurable_const

omit [CompleteSpace H] in
private theorem conditionalStar_measurable (ε : ℝ) (n : ℕ) :
    MeasurableSet (conditionalStar (H := H) ε n) := by
  rw [conditionalStar, ofPred_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le
    (continuous_fst.inner ((continuous_apply j).comp continuous_snd)).measurable measurable_const

omit [CompleteSpace H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] in
private theorem conditionalStar_indicator (ε : ℝ) (n : ℕ) (p : H × (Fin n → H)) :
    (conditionalStar ε n).indicator (fun _ => (1:ℝ)) p =
      ∏ j : Fin n, (negativeNeighbors ε p.1).indicator (fun _ => (1:ℝ)) (p.2 j) := by
  classical
  by_cases hp : p ∈ conditionalStar ε n
  · rw [indicator_of_mem hp]
    symm
    apply Finset.prod_eq_one
    intro j hj
    change (negativeNeighbors ε p.1).indicator (fun _ : H => (1:ℝ)) (p.2 j) = 1
    rw [indicator_of_mem (show p.2 j ∈ negativeNeighbors ε p.1 from hp j)]
  · rw [indicator_of_notMem hp]
    have hnot : ¬∀ j : Fin n, p.2 j ∈ negativeNeighbors ε p.1 := hp
    obtain ⟨j,hj⟩ := not_forall.mp hnot
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact indicator_of_notMem hj (fun _ : H => (1:ℝ))

omit [CompleteSpace H] in
/-- Exact conditional-probability identity for the genuine finite product law. -/
theorem negativeStar_mass_eq_integral (ν : Measure H) [IsProbabilityMeasure ν]
    (ε : ℝ) (n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => ν)).real (negativeStar (H := H) ε n) =
      ∫ z, (negativeNeighborMass ν ε z)^n ∂ν := by
  let μ := Measure.pi (fun _ : Fin (n+1) => ν)
  let η := Measure.pi (fun _ : Fin n => ν)
  have hstar := negativeStar_measurable (H := H) ε n
  have hcond := conditionalStar_measurable (H := H) ε n
  have hmass : μ.real (negativeStar ε n) =
      ∫ σ, (negativeStar ε n).indicator (fun _ => (1:ℝ)) σ ∂μ := by
    rw [integral_indicator_const 1 hstar, smul_eq_mul, mul_one]
  have htrans : (∫ σ, (negativeStar ε n).indicator (fun _ => (1:ℝ)) σ ∂μ) =
      ∫ p, (conditionalStar ε n).indicator (fun _ => (1:ℝ)) p ∂ν.prod η := by
    rw [← ((measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => ν) 0).symm).integral_comp']
    simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      Fin.insertNth_zero, Equiv.coe_fn_mk, cast_eq]
    apply integral_congr_ae
    exact .of_forall fun p => by
      change (negativeStar ε n).indicator (fun _ => (1:ℝ)) (Fin.cons p.1 p.2) =
        (conditionalStar ε n).indicator (fun _ => (1:ℝ)) p
      have hmem : Fin.cons p.1 p.2 ∈ negativeStar ε n ↔ p ∈ conditionalStar ε n := by
        simp only [negativeStar, conditionalStar, mem_ofPred_eq, Fin.cons_zero, Fin.cons_succ]
      by_cases hp : p ∈ conditionalStar ε n
      · rw [indicator_of_mem hp, indicator_of_mem (hmem.mpr hp)]
      · rw [indicator_of_notMem hp, indicator_of_notMem (fun h => hp (hmem.mp h))]
  have hrow (z : H) :
      (∫ y, (conditionalStar ε n).indicator (fun _ => (1:ℝ)) (z,y) ∂η) =
        (negativeNeighborMass ν ε z)^n := by
    simp_rw [conditionalStar_indicator]
    rw [integral_fin_nat_prod_eq_prod]
    simp only [integral_indicator_const (1:ℝ) (negativeNeighbors_measurable ε z),
      smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  rw [hmass, htrans, integral_prod _ ((integrable_const 1).indicator hcond)]
  simp_rw [hrow]

/-- Panchenko's genuine negative-star geometric bound. It applies to
arbitrary probability laws in the unit ball, including Gibbs laws. -/
theorem negativeStar_mass_le (ν : Measure H) [IsProbabilityMeasure ν]
    (hν : ∀ᵐ z ∂ν, ‖z‖ ≤ 1) {ε γ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (n : ℕ) :
    (Measure.pi (fun _ : Fin (n+1) => ν)).real (negativeStar (H := H) ε n) ≤
      2*(1-γ)/ε+γ^n := by
  rw [negativeStar_mass_eq_integral]
  let U := badCenters ν ε γ
  have hU := badCenters_measurable ν ε γ
  have hm := negativeNeighborMass_measurable ν ε
  have hi : Integrable (fun z => (negativeNeighborMass ν ε z)^n) ν := by
    apply Integrable.of_bound (hm.pow_const n).aestronglyMeasurable 1
    exact .of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (negativeNeighborMass_nonneg ν ε z) n)]
      exact pow_le_one₀ (negativeNeighborMass_nonneg ν ε z) (negativeNeighborMass_le_one ν ε z)
  have hI := (integrable_const (μ := ν) (1:ℝ)).indicator hU
  have hupper := integral_mono_ae hi ((integrable_const (γ^n)).add hI) (.of_forall fun z => by
    change (negativeNeighborMass ν ε z)^n ≤ γ^n+U.indicator (fun _ => (1:ℝ)) z
    by_cases hz : z ∈ U
    · rw [indicator_of_mem hz]
      have hp : (negativeNeighborMass ν ε z)^n ≤ 1 :=
        pow_le_one₀ (negativeNeighborMass_nonneg ν ε z) (negativeNeighborMass_le_one ν ε z)
      nlinarith [pow_nonneg hγ.le n]
    · rw [indicator_of_notMem hz, add_zero]
      have hlt : negativeNeighborMass ν ε z < γ := lt_of_not_ge hz
      exact pow_le_pow_left₀ (negativeNeighborMass_nonneg ν ε z) hlt.le n)
  change (∫ z, (negativeNeighborMass ν ε z)^n ∂ν) ≤
    ∫ z, γ^n+U.indicator (fun _ => (1:ℝ)) z ∂ν at hupper
  rw [integral_add (integrable_const (γ^n)) hI, integral_const, probReal_univ, one_smul,
    integral_indicator_const 1 hU, smul_eq_mul, mul_one] at hupper
  have hbad := badCenters_mass_le ν hν hε hε1 hγ hγ1
  change ν.real U ≤ 2*(1-γ)/ε at hbad
  linarith

end SlowEquilibration.GaussianNegativeStarGeometry
