-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTaylorBandGeometry
public import SlowEquilibration.SphericalLatitudeCountIntegral
public import SlowEquilibration.SphericalGibbs

@[expose] public section

/-! Borel dependence of the literal Householder transverse frame and actual
Taylor-band partition on the original disorder and candidate bottom point. -/

namespace SlowEquilibration.SphericalTaylorRemainder
noncomputable section
open MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.SphericalLatitudeChartKacRice
open scoped RealInnerProductSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem latitudeFrameAt_jointMeasurable (n : ℕ) :
    Measurable (fun p : Vector (n+1) × Vector n => latitudeFrameAt p.1 p.2) := by
  change Measurable (fun p : Vector (n+1) × Vector n =>
    ((ℝ ∙ (latitudeChartPole n-p.1))ᗮ).reflection (latitudeChartFrame n p.2))
  have hframe := (latitudeChartFrame n).continuous.measurable
  simp only [Submodule.reflection_orthogonal_apply,Submodule.reflection_singleton_apply]
  have hu : Measurable (fun p : Vector (n+1) × Vector n => latitudeChartPole n-p.1) :=
    measurable_const.sub measurable_fst
  have hv : Measurable (fun p : Vector (n+1) × Vector n => latitudeChartFrame n p.2) :=
    hframe.comp measurable_snd
  convert ((((hu.inner hv).div (hu.norm.pow_const 2)).const_smul (2 : ℕ)).smul hu |>.sub hv).neg using 1
  funext p
  simp [two_smul,add_smul]

theorem bottomTransverseFrame_jointMeasurable {n : ℕ}
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) :
    Measurable (fun p : Vector (n+1) × Vector n => bottomTransverseFrame e p.1 p.2) :=
  e.continuous.measurable.comp (latitudeFrameAt_jointMeasurable n)

def transverseRemainderField {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q : ℝ) (J : Disorder (n+2) P)
    (y : Vector (n+1)) (z : Vector n) : ℝ :=
  taylorRemainderCLM c (latitudeMap w e q y)
    (transverseOffset (bottomTransverseFrame e y) Q z) (euclideanDisorder J)

theorem transverseRemainderField_jointMeasurable {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q : ℝ) :
    Measurable (fun p : (Disorder (n+2) P × Vector (n+1)) × Vector n =>
      transverseRemainderField c w e q Q p.1.1 p.1.2 p.2) := by
  let m : (Disorder (n+2) P × Vector (n+1)) × Vector n → Vector (n+2) :=
    fun p => latitudeMap w e q p.1.2
  let z : (Disorder (n+2) P × Vector (n+1)) × Vector n → Vector (n+2) :=
    fun p => transverseOffset (bottomTransverseFrame e p.1.2) Q p.2
  have hm : Measurable m := (latitudeMap_continuous w e q).measurable.comp (measurable_snd.comp measurable_fst)
  have hz : Measurable z := by
    unfold z transverseOffset
    exact (bottomTransverseFrame_jointMeasurable e).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd) |>.const_smul
        (Real.sqrt (((n+2 : ℕ) : ℝ)*(1-Q)/(Q*(n : ℝ))))
  have hfield₁ := (field_jointContinuous c).measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk (hm.add hz))
  have hfield₀ := (field_jointContinuous c).measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk hm)
  have hderiv := (directionalJet_jointContinuous c).measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk (hm.prodMk hz))
  have hh := (hfield₁.sub hfield₀).sub hderiv
  convert hh using 1
  funext p
  simp only [transverseRemainderField,taylorRemainderCLM_actual,Function.comp_def,
    jet,iteratedFDeriv_one_apply,m,z,Pi.add_apply,Pi.sub_apply]

def transverseRemainderPressure {n P : ℕ} (c : Degree P → ℝ) (w : Vector (n+2))
    (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q β : ℝ)
    (J : Disorder (n+2) P) (y : Vector (n+1)) : ℝ :=
  Real.log (partition n β (transverseRemainderField c w e q Q J y))/((n+2 : ℕ) : ℝ)

theorem transverseRemainderPressure_jointMeasurable {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q β : ℝ) :
    Measurable (fun p : Disorder (n+2) P × Vector (n+1) =>
      transverseRemainderPressure c w e q Q β p.1 p.2) := by
  have hf := ((transverseRemainderField_jointMeasurable c w e q Q).const_mul β).exp
  have hi := (hf.stronglyMeasurable.integral_prod_right' (ν := sphereLaw n)).measurable
  exact hi.log.div_const _

theorem measurableSet_transverseRemainder_bad {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q Q β M : ℝ) :
    MeasurableSet {p : Disorder (n+2) P × Vector (n+1) |
      transverseRemainderPressure c w e q Q β p.1 p.2<M} :=
  measurableSet_lt (transverseRemainderPressure_jointMeasurable c w e q Q β) measurable_const

end
end SlowEquilibration.SphericalTaylorRemainder
