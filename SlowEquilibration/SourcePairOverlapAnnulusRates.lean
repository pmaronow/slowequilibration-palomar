-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedOverlapPairTail

/-! The source annulus error rate on the actual product uniform sphere
law, including its exact exp(-N^(1-2*alpha)/4) exponent. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel
open scoped Topology ENNReal
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

lemma ambient_overlap_cutoff_square (n:ℕ) (α:ℝ) :
    ((n+3:ℕ):ℝ)*(((n+3:ℕ):ℝ)^(-α))^2=((n+3:ℕ):ℝ)^(1-2*α):=by
  have hN:0<((n+3:ℕ):ℝ):=by positivity
  rw [←Real.rpow_two,←Real.rpow_mul hN.le,show -α*2=-2*α by ring]
  calc
    _ = ((n+3:ℕ):ℝ)^(1:ℝ)*((n+3:ℕ):ℝ)^(-2*α):=by rw [Real.rpow_one]
    _ = _:=by rw [←Real.rpow_add hN];congr 1;ring

theorem source_sphere_pair_annulus_rate (α:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      (∫ p:Vector (n+3)×Vector (n+3),
        {p:Vector (n+3)×Vector (n+3) | ((n+3:ℕ):ℝ)^(-α)< |overlap p.1 p.2|}.indicator
          (fun p=>Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8)) p
          ∂(sphereLaw (n+3)).prod (sphereLaw (n+3))) ≤
        C*Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4):=by
  obtain ⟨C,hC,hall⟩:=sphere_pair_weighted_overlap_tail_eventually_le
    (a:=1/8) (b:=3/8) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 3).eventually hall] with n hn
  have hh:=hn (((n+3:ℕ):ℝ)^(-α)) (Real.rpow_nonneg (by positivity) _)
  have hexp:-(3/8-1/8)*((n+3:ℕ):ℝ)*(((n+3:ℕ):ℝ)^(-α))^2=
      -((n+3:ℕ):ℝ)^(1-2*α)/4:=by
    rw [show -(3/8-1/8)*((n+3:ℕ):ℝ)*(((n+3:ℕ):ℝ)^(-α))^2=
      -(((n+3:ℕ):ℝ)*(((n+3:ℕ):ℝ)^(-α))^2)/4 by ring,ambient_overlap_cutoff_square]
  rw [hexp] at hh
  have hPoint (p:Vector (n+3)×Vector (n+3)):
      Real.exp ((1/8:ℝ)*((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2)=
        Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8):=by congr 1;ring
  simpa only [hPoint] using hh

theorem source_sphere_pair_annulus_lintegral_rate (α:ℝ) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,
      (∫⁻ p:Vector (n+3)×Vector (n+3),
        {p:Vector (n+3)×Vector (n+3) | ((n+3:ℕ):ℝ)^(-α)< |overlap p.1 p.2|}.indicator
          (fun p=>ENNReal.ofReal (Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8))) p
          ∂(sphereLaw (n+3)).prod (sphereLaw (n+3))) ≤
        ENNReal.ofReal (C*Real.exp (-((n+3:ℕ):ℝ)^(1-2*α)/4)):=by
  obtain ⟨C,hC,hall⟩:=source_sphere_pair_annulus_rate α
  refine ⟨C,hC,?_⟩
  filter_upwards [hall] with n hn
  let A:={p:Vector (n+3)×Vector (n+3) | ((n+3:ℕ):ℝ)^(-α)< |overlap p.1 p.2|}
  have hA:MeasurableSet A:=measurableSet_lt measurable_const (by unfold overlap;fun_prop)
  have hF:Continuous (fun p:Vector (n+3)×Vector (n+3)=>
    Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8)):=by unfold overlap;fun_prop
  have hi:=((memLp_spherePair_continuous (by omega) hF 1).integrable le_rfl).indicator hA
  have he:=ofReal_integral_eq_lintegral_ofReal hi
    (.of_forall (fun p=>Set.indicator_nonneg (fun _ _=>(Real.exp_pos _).le) p))
  have hPoint (p:Vector (n+3)×Vector (n+3)):
      ENNReal.ofReal (A.indicator (fun p=>Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8)) p)=
        A.indicator (fun p=>ENNReal.ofReal (Real.exp (((n+3:ℕ):ℝ)*(overlap p.1 p.2)^2/8))) p:=by
    by_cases hp:p∈A
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp,ENNReal.ofReal_zero]
  simp only [hPoint] at he
  rw [←he]
  exact ENNReal.ofReal_le_ofReal hn

end
end SlowEquilibration.PairConditionalDeterminantMoments
