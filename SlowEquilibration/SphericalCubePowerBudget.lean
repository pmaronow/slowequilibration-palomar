-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPositiveParameterCube

/-! Actual coordinate and full-cube averages of tensor power-GG errors.
The bounds consume the proved Gaussian deviation budget and the exact
joint Gibbs coordinate-slice identity. No GG smallness assumption occurs. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianPerturbationDeviation

open MeasureTheory Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual deviation is integrable under the normalized positive
parameter law, including its endpoints. -/
theorem totalDeviation_integrable_positiveParameterLaw {V ι : Type*}
    [MeasurableSpace V] [Fintype ι] [DecidableEq ι]
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ z ∂ν,‖L z‖≤K) (label : ι → Bool) :
    Integrable (totalDeviation ν L label) positiveParameterLaw := by
  rw [positiveParameterLaw]
  apply Integrable.smul_measure
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1/2:ℝ)≤1)).mp
      (totalDeviation_intervalIntegrable ν L hL hK hb label (1/2) 1)
  · norm_num

end SlowEquilibration.GaussianPerturbationDeviation

namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianReplicaCalculus GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationDeviation GaussianPerturbationIntegrated
open GaussianGGEnsemble
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual uniform one-coordinate power-GG average. The numerical
parameters r,y are independent of dimension, base law and replica test. -/
theorem coordinate_cubePowerDefect_integral_le {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0<v)
    (x : Fin K → ℝ) (hx : ∀p,|x p|≤2) (p : Fin K) (ε : ℝ) (m : ℕ)
    {r y : ℝ} (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    (∫t,cubePowerDefect ν v ε m (p.val+1) (Function.update x p t) ∂positiveParameterLaw)≤
      (4/(v^2*(1/4:ℝ)^(p.val+1)))*
        ((v^2+r^2)/(2*r)+8*v^2*y+36*Real.exp (1/2)*v/y) := by
  let L := unitLinear (N := N) (coefficients v (Function.update x p 1))
  let a : ℝ := v^2*(1/4:ℝ)^(p.val+1)
  have ha : 0<a := by dsimp [a];positivity
  have hL : Measurable L := unitLinear_measurable _
  have hB : ∀ᵐ z ∂ν,‖L z‖≤2*v := .of_forall (unitLinear_norm_bound hv.le _ (update_one_abs_le_two x hx p))
  have hiDev := totalDeviation_integrable_positiveParameterLaw ν L hL (by positivity) hB (degreeLabel p)
  have hDiag : ∀ᵐ z ∂ν,(∑i,if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable L i z)^2 else 0)≤v^2 := .of_forall fun z => by
    change (∑i,if degreeLabel p i=true then
      (GaussianSpinComparison.coordinateObservable (linear (coefficients v (Function.update x p 1))) i z.val)^2 else 0)≤v^2
    exact active_diagonal_le_v_sq v (Function.update x p 1) p (Function.update_self p 1 x) z.val z.property
  have hBudget := totalDeviation_positive_integral_le ν L hL (by positivity : 0<2*v) hB
    (sq_nonneg v) (degreeLabel p) hDiag hr hy hy1
  let F : ℝ → ℝ := fun t => cubePowerDefect ν v ε m (p.val+1) (Function.update x p t)
  have hm : Measurable F := by
    have hu : Measurable (fun t : ℝ => Function.update x p t) := by
      simpa only [Function.comp_def,id_eq] using
        (FiniteCubeFubini.update_joint_measurable K p).comp (measurable_const.prodMk measurable_id)
    simpa only [F,Function.comp_def] using (cubePowerDefect_measurable ν hv.le ε m (p.val+1)).comp hu
  have hi : Integrable F positiveParameterLaw := by
    apply Integrable.of_bound hm.aestronglyMeasurable 2
    exact .of_forall fun t => by
      change |cubePowerDefect ν v ε m (p.val+1) (Function.update x p t)|≤2
      rw [abs_of_nonneg (cubePowerDefect_nonneg _ _ _ _ _ _)]
      exact cubePowerDefect_le_two ν hv.le ε m (p.val+1) _
  have hpoint : ∀ᵐ t ∂positiveParameterLaw, F t≤(2/a)*totalDeviation ν L (degreeLabel p) t := by
    filter_upwards [positiveParameterLaw_support] with t ht
    have htpos : 0<t := by linarith [ht.1]
    have hs := cubePowerDefect_coordinate_le ν hv x hx p t htpos ε m
    have hnt : (1/2:ℝ)≤((m:ℝ)+1)*t := by nlinarith [show (0:ℝ)≤(m:ℝ) from Nat.cast_nonneg m,ht.1]
    have hδ : 0≤totalDeviation ν L (degreeLabel p) t := totalDeviation_nonneg _ _ _ _
    have hden : 0<((m:ℝ)+1)*t*a := by positivity
    have hd : totalDeviation ν L (degreeLabel p) t/(((m:ℝ)+1)*t*a)≤
        (2/a)*totalDeviation ν L (degreeLabel p) t := by
      apply (div_le_iff₀ hden).mpr
      have heq : ((2/a)*totalDeviation ν L (degreeLabel p) t)*(((m:ℝ)+1)*t*a)=
          (2*((m:ℝ)+1)*t)*totalDeviation ν L (degreeLabel p) t := by
        field_simp [ha.ne']
      rw [heq]
      nlinarith
    exact hs.trans hd
  have hIntegral := integral_mono_ae hi (hiDev.const_mul (2/a)) hpoint
  rw [integral_const_mul] at hIntegral
  have hscaled := mul_le_mul_of_nonneg_left hBudget (by positivity : 0≤2/a)
  change (∫t,F t ∂positiveParameterLaw)≤_ at hIntegral ⊢
  calc
    _ ≤ (2/a)*(∫t,totalDeviation ν L (degreeLabel p) t ∂positiveParameterLaw) := hIntegral
    _ ≤ (2/a)*(2*((v^2+r^2)/(2*r)+8*v^2*y+18*Real.exp (1/2)*(2*v)/y)) := hscaled
    _ = _ := by dsimp [a];ring

/-- Fubini over the genuine finite cube gives the actual averaged GG
bound for every positive-degree test, uniformly in the base law and N. -/
theorem cubeMeanPowerDefect_le {N K : ℕ}
    (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν] {v : ℝ} (hv : 0<v)
    (p : Fin K) (ε : ℝ) (m : ℕ) {r y : ℝ} (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    cubeMeanPowerDefect (K := K) ν v ε m (p.val+1)≤
      (4/(v^2*(1/4:ℝ)^(p.val+1)))*
        ((v^2+r^2)/(2*r)+8*v^2*y+36*Real.exp (1/2)*v/y) := by
  apply FiniteCubeFubini.integral_le_of_coordinate_bound positiveParameterLaw p
    (cubePowerDefect ν v ε m (p.val+1)) (cubePowerDefect_measurable ν hv.le ε m (p.val+1))
    (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (cubePowerDefect_nonneg _ _ _ _ _ _)]
      exact cubePowerDefect_le_two ν hv.le ε m (p.val+1) x)
  filter_upwards [positiveCubeLaw_abs_le_two K] with x hx
  exact coordinate_cubePowerDefect_integral_le ν hv x hx p ε m hr hy hy1

end SlowEquilibration.SphericalPositivePerturbation
