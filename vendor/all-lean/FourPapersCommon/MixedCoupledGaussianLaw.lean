module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedCoupledConcentration
public import Targets.CoupledGaussianLaw

@[expose] public section

/-! Actual mixed-disorder spectral law, jointly with an independent outer field.

The covariance-independent coordinate argument adapts the Apache-2.0
`Targets.CoupledGaussianLaw` proof. It applies to the genuine mixed Gaussian
record; no SK covariance identity is used.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
variable {n k : ℕ} {ξ : AdmissibleEvenMixture}
set_option maxHeartbeats 800000

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
theorem mixedDisorder_spectral_map (sk : MixedDisorder (Ω := Ω) n ξ) :
    (Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map
      (fun z => ∑ i, (Real.sqrt (sk.hU.τ i) * z i) • sk.hU.w i) =
      (ℙ : Measure Ω).map sk.U := by
  let C : Ω → (sk.hU.ι → ℝ) := fun ω i => sk.hU.c i ω
  let S : (sk.hU.ι → ℝ) → (sk.hU.ι → ℝ) := fun z i => Real.sqrt (sk.hU.τ i) * z i
  let W : (sk.hU.ι → ℝ) → EnergySpace n := fun z => ∑ i, z i • sk.hU.w i
  have hC : Measurable C := Measurable.of_eval sk.hU.c_meas
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hW : Measurable W := by dsimp [W]; fun_prop
  have hClaw : (ℙ : Measure Ω).map C = Measure.pi (fun i => gaussianReal 0 (sk.hU.τ i)) := by
    have H := iIndepFun.map_fun_eq_pi_map (fun i => (sk.hU.c_meas i).aemeasurable) sk.hU.c_indep
    simpa only [show ∀ i, (ℙ : Measure Ω).map (sk.hU.c i) = gaussianReal 0 (sk.hU.τ i)
      from sk.hU.c_gauss] using H
  have hSlaw : (Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map S =
      Measure.pi (fun i => gaussianReal 0 (sk.hU.τ i)) := by
    haveI (i : sk.hU.ι) : IsProbabilityMeasure
        ((gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (sk.hU.τ i) * z)) := by
      rw [gaussianReal_map_sqrt]
      infer_instance
    rw [show S = (fun z i => Real.sqrt (sk.hU.τ i) * z i) from rfl,
      Measure.pi_map_pi (μ := fun _ : sk.hU.ι => gaussianReal 0 1)
        (f := fun i z => Real.sqrt (sk.hU.τ i) * z)
        (fun i => (measurable_const.mul measurable_id).aemeasurable)]
    simp only [gaussianReal_map_sqrt]
  calc
    _ = ((Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)).map S).map W := by
      rw [Measure.map_map hW hS]
      rfl
    _ = ((ℙ : Measure Ω).map C).map W := by rw [hSlaw, hClaw]
    _ = (ℙ : Measure Ω).map sk.U := by
      rw [Measure.map_map hW hC]
      congr 1
      exact sk.hU.repr.symm

omit [IsProbabilityMeasure (ℙ : Measure Ω)] in
/-- The law is preserved jointly with the independent, as yet unscaled outer field. -/
theorem mixedCoupledGaussian_pair_map (sk : MixedDisorder (Ω := Ω) n ξ) :
    (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)).map
      (fun z => (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i))) =
      ((ℙ : Measure Ω).map sk.U).prod (piGauss n) := by
  let μ := Measure.pi (fun _ : sk.hU.ι => gaussianReal 0 1)
  let ν := Measure.pi (fun _ : sk.hU.ι ⊕ Fin n => gaussianReal 0 1)
  let W : (sk.hU.ι → ℝ) → EnergySpace n :=
    fun z => ∑ i, (Real.sqrt (sk.hU.τ i) * z i) • sk.hU.w i
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : sk.hU.ι ⊕ Fin n => ℝ)
  have hW : Measurable W := by dsimp [W]; fun_prop
  have he : ν.map e = μ.prod (piGauss n) :=
    (measurePreserving_sumPiEquivProdPi (fun _ : sk.hU.ι ⊕ Fin n => gaussianReal 0 1)).map_eq
  have hto : Measurable (WithLp.toLp 2 : (sk.hU.ι ⊕ Fin n → ℝ) → MixedCoupledGaussianSpace sk) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : sk.hU.ι ⊕ Fin n => ℝ)).symm.continuous.measurable
  have hpair : Measurable (fun z : MixedCoupledGaussianSpace sk =>
      (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold mixedCoupledGaussianU
    fun_prop
  rw [SYK.standardGaussianMeasureOnEuclidean, Measure.map_map hpair hto]
  change ν.map _ = _
  calc
    _ = (ν.map e).map (Prod.map W id) := by
      rw [Measure.map_map (hW.prodMap measurable_id) e.measurable]
      rfl
    _ = (μ.map W).prod (piGauss n) := by
      rw [he, ← Measure.map_prod_map μ (piGauss n) hW measurable_id, Measure.map_id]
    _ = _ := by rw [mixedDisorder_spectral_map sk]

/-- Change of coordinates for any jointly measurable disorder/outer-field test. -/
theorem integral_mixedCoupledGaussian_pair (sk : MixedDisorder (Ω := Ω) n ξ)
    {F : EnergySpace n × (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    (∫ z, F (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i))
      ∂SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) =
      ∫ p : Ω × (Fin n → ℝ), F (sk.U p.1, p.2) ∂(ℙ : Measure Ω).prod (piGauss n) := by
  have hpair : Measurable (fun z : MixedCoupledGaussianSpace sk =>
      (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold mixedCoupledGaussianU
    fun_prop
  rw [← integral_map hpair.aemeasurable hF.aestronglyMeasurable, mixedCoupledGaussian_pair_map,
    ← Measure.map_id (μ := piGauss n),
    Measure.map_prod_map _ _ sk.hU.repr_measurable measurable_id,
    integral_map (sk.hU.repr_measurable.prodMap measurable_id).aemeasurable hF.aestronglyMeasurable]
  simp only [Measure.map_id]
  rfl

theorem integrable_mixedCoupledGaussian_pair_iff (sk : MixedDisorder (Ω := Ω) n ξ)
    {F : EnergySpace n × (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Integrable (fun z => F (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i)))
      (SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n)) ↔
    Integrable (fun p : Ω × (Fin n → ℝ) => F (sk.U p.1, p.2))
      ((ℙ : Measure Ω).prod (piGauss n)) := by
  have hpair : Measurable (fun z : MixedCoupledGaussianSpace sk =>
      (mixedCoupledGaussianU sk z, fun i => z (Sum.inr i))) := by
    unfold mixedCoupledGaussianU
    fun_prop
  have H := integrable_map_measure
    (μ := SYK.standardGaussianMeasureOnEuclidean (sk.hU.ι ⊕ Fin n))
    hF.aestronglyMeasurable hpair.aemeasurable
  rw [mixedCoupledGaussian_pair_map, ← Measure.map_id (μ := piGauss n),
    Measure.map_prod_map _ _ sk.hU.repr_measurable measurable_id] at H
  have H' := integrable_map_measure (μ := (ℙ : Measure Ω).prod (piGauss n))
    hF.aestronglyMeasurable (sk.hU.repr_measurable.prodMap measurable_id).aemeasurable
  exact H.symm.trans H'


end FourPapersCommon
