-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.FiniteTensorMixtureMaximum
public import SlowEquilibration.GaussianNormConcentration

/-! Sharp finite Gaussian tails for the genuine aggregate tensor supremum. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.FiniteTensorMixtureMaximum
open MeasureTheory Set
open scoped RealInnerProductSpace
open PureTensorJetBounds GaussianCompactMaximum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem absoluteSupremum_lipschitz {N : ℕ} (hN : 0<N) (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0≤c i) {v : ℝ} (hv : 0≤v) (hvar : (∑ i,c i)≤v) :
    LipschitzWith (Real.sqrt ((N:ℝ)*v)).toNNReal
      (absoluteSupremum (fun x : UnitSphere N => feature d c x.val)) := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  apply field_supremum_lipschitz (fun x => innerSL ℝ
    (signedFeature (fun x : UnitSphere N => feature d c x.val) x))
  intro x
  simp only [innerSL_apply_norm,signedFeature,norm_smul,Real.norm_eq_abs,abs_sign,one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [feature_norm_sq d c hc,Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hv)]
  exact mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg N)

theorem absoluteSupremum_upper_tail {N : ℕ} (hN : 0<N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0≤c i) (hd : ∀ i,1≤d i)
    {s v t : ℝ} (hs : 0≤s) (hv : 0≤v) (ht : 0≤t)
    (hmoment : (∑ i,(d i:ℝ)*c i)≤s) (hvar : (∑ i,c i)≤v) :
    (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))
      {g|2*N*Real.sqrt s+t<absoluteSupremum (fun x : UnitSphere N => feature d c x.val) g}≤
      ENNReal.ofReal (Real.exp (-t^2/(2*N*v))) := by
  let F := absoluteSupremum (fun x : UnitSphere N => feature d c x.val)
  have hLip := absoluteSupremum_lipschitz hN d c hc hv hvar
  have hm : (∫ g,F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))≤2*N*Real.sqrt s :=
    (expected_absoluteSupremum_le hN d c hc hd).trans (by gcongr)
  have htail := GaussianNormConcentration.centered_lipschitz_upper_tail F
    (Real.sqrt_nonneg _) hLip ht
  rw [Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hv)] at htail
  have hreal : (SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)).real
      {g|2*N*Real.sqrt s+t<F g}≤Real.exp (-t^2/(2*N*v)) := by
    apply (measureReal_mono (show {g|2*N*Real.sqrt s+t<F g}⊆
      {g|(∫ g,F g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))+t≤F g}
      from fun g hg => by change _<_ at hg;change _≤_;linarith)).trans
    simpa only [mul_assoc] using htail
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

end SlowEquilibration.FiniteTensorMixtureMaximum
