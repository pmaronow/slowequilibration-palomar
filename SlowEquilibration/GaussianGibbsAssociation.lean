-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinKernels

/-! Exact association of ordinary Gaussian Gibbs tilts. Conditioning a
bank of Gaussian coordinates gives its actual Gibbs spin law, which may
then be used as the base law of an independent perturbation bank. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianSpinInterpolation

open MeasureTheory Set
open scoped Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V H₁ H₂ H₃ : Type*} [MeasurableSpace V]
  [NormedAddCommGroup H₁] [NormedSpace ℝ H₁] [CompleteSpace H₁] [FiniteDimensional ℝ H₁]
  [NormedAddCommGroup H₂] [NormedSpace ℝ H₂] [CompleteSpace H₂] [FiniteDimensional ℝ H₂]
  [NormedAddCommGroup H₃] [NormedSpace ℝ H₃] [CompleteSpace H₃] [FiniteDimensional ℝ H₃]

omit [CompleteSpace H₂] [FiniteDimensional ℝ H₂] [CompleteSpace H₃] [FiniteDimensional ℝ H₃] in
/-- The true partition integral after conditioning the first field bank
is the combined partition divided by the first bank's partition. -/
theorem moment_gibbsMeasure_split (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H₁ →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ z ∂ν,‖L z‖≤K) (w : H₁)
    (M : V → H₂ →L[ℝ] ℝ) (z : H₂)
    (T : V → H₃ →L[ℝ] ℝ) (u : H₃)
    (hsplit : ∀ᵐ x ∂ν,T x u=L x w+M x z) :
    moment (gibbsMeasure ν L w) (fun _ => 1) M z=
      moment ν (fun _ => 1) T u/moment ν (fun _ => 1) L w := by
  unfold moment
  simp only [weight,one_mul]
  rw [integral_gibbsMeasure ν L hL hb w (fun x => Real.exp (M x z))]
  unfold expectation moment
  simp only [weight,one_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hsplit] with x hx
  rw [hx,Real.exp_add,mul_comm]

omit [CompleteSpace H₂] [FiniteDimensional ℝ H₂] in
/-- Association for actual Gibbs laws. The field split is an ordinary
pointwise field identity; normalization and both density products are
proved, rather than supplied as a conditional Gibbs-law assumption. -/
theorem gibbsMeasure_associate (ν : Measure V) [IsFiniteMeasure ν] [NeZero ν]
    (L : V → H₁ →L[ℝ] ℝ) (hL : Measurable L) {K : ℝ}
    (hb : ∀ᵐ x ∂ν,‖L x‖≤K) (w : H₁)
    (M : V → H₂ →L[ℝ] ℝ) (hM : Measurable M) (z : H₂)
    (T : V → H₃ →L[ℝ] ℝ) (hT : Measurable T) {KT : ℝ}
    (hbT : ∀ᵐ x ∂ν,‖T x‖≤KT) (u : H₃)
    (hsplit : ∀ᵐ x ∂ν,T x u=L x w+M x z) :
    gibbsMeasure (gibbsMeasure ν L w) M z=gibbsMeasure ν T u := by
  have hZ := moment_gibbsMeasure_split ν L hL hb w M z T u hsplit
  have hLpos := moment_one_pos ν L hL hb w
  have hTpos := moment_one_pos ν T hT hbT u
  have hdL : Measurable (fun x => ENNReal.ofReal
      (Real.exp (L x w)/moment ν (fun _ => 1) L w)) :=
    (((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp.div_const _).ennreal_ofReal
  have hdM : Measurable (fun x => ENNReal.ofReal
      (Real.exp (M x z)/(moment ν (fun _ => 1) T u/moment ν (fun _ => 1) L w))) :=
    (((ContinuousLinearMap.apply ℝ ℝ z).continuous.measurable.comp hM).exp.div_const _).ennreal_ofReal
  change (gibbsMeasure ν L w).withDensity (fun x => ENNReal.ofReal
    (Real.exp (M x z)/moment (gibbsMeasure ν L w) (fun _ => 1) M z))=_
  rw [hZ,gibbsMeasure,← withDensity_mul ν hdL hdM]
  apply withDensity_congr_ae
  filter_upwards [hsplit] with x hx
  change ENNReal.ofReal (Real.exp (L x w)/moment ν (fun _ => 1) L w)*
    ENNReal.ofReal (Real.exp (M x z)/(moment ν (fun _ => 1) T u/moment ν (fun _ => 1) L w))=
    ENNReal.ofReal (Real.exp (T x u)/moment ν (fun _ => 1) T u)
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [hx,Real.exp_add]
  field_simp [hLpos.ne',hTpos.ne']

end SlowEquilibration.GaussianSpinInterpolation
