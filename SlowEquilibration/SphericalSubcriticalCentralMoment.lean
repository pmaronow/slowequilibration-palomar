-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureSubcriticalQuadratic
public import SlowEquilibration.SphericalSubcriticalOverlapMoment
public import SlowEquilibration.SphericalCentralOverlapPerturbation

@[expose] public section

/-! Actual bounded central second moments throughout the full strict RS
region. Quadratic terms and odd degrees are retained literally. -/

noncomputable section
namespace SlowEquilibration.SphericalModel
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- The genuine pair exponential moment has a uniform bound for every fixed
subcritical quadratic budget, with no reference-vector premise. -/
theorem sphere_pair_exp_square_eventually_bounded {b : ℝ}
    (hb : 0≤b) (hsub : b<1/2) :
    ∃C>0,∀ᶠ N : ℕ in atTop,
      (∫z : Vector N×Vector N,Real.exp (b*(N:ℝ)*(overlap z.1 z.2)^2)
        ∂(sphereLaw N).prod (sphereLaw N))≤C := by
  obtain ⟨C,hC,hbound⟩ := sphere_overlap_exp_square_eventually_bounded hb hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with N hNbound hN
  have hf : Continuous (fun z : Vector N×Vector N =>
      Real.exp (b*(N:ℝ)*(overlap z.1 z.2)^2)) := by unfold overlap; fun_prop
  rw [integral_prod _ ((memLp_spherePair_continuous hN hf 1).integrable le_rfl)]
  calc
    _ ≤ ∫_x : Vector N,C ∂sphereLaw N := by
      apply integral_mono_of_nonneg (.of_forall fun _ => integral_nonneg fun _ => (Real.exp_pos _).le)
        (integrable_const _)
      filter_upwards [sphereLaw_support hN] with x hx
      exact hNbound x hx
    _ = _ := by simp

/-- The actual central HS term is uniformly bounded, with a window chosen
before N, for all finite mixtures strictly below their actual static threshold. -/
theorem centralOverlapMoment_eventually_bounded (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    ∃δ∈Ioo (0:ℝ) 1,∃C>0,∀ᶠ N : ℕ in atTop,
      centralOverlapMoment N (mixtureCoefficients μ) β δ≤C := by
  obtain ⟨δ,hδ,κ,hκ,hbudget,hwindow⟩ := μ.exists_subcritical_quadratic_window hβ hβs
  obtain ⟨C,hC,hbound⟩ := sphere_pair_exp_square_eventually_bounded
    (mul_nonneg (sq_nonneg β) hκ.le) hbudget
  refine ⟨δ,hδ,C,hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with N hNbound hN
  have hg : Continuous (fun z : Vector N×Vector N =>
      Real.exp ((β^2*κ)*(N:ℝ)*(overlap z.1 z.2)^2)) := by unfold overlap; fun_prop
  apply le_trans _ hNbound
  unfold centralOverlapMoment
  apply integral_mono_of_nonneg
    (.of_forall fun z => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) z)
    ((memLp_spherePair_continuous hN hg 1).integrable le_rfl)
  filter_upwards [] with z
  by_cases hz : z∈smallOverlap δ
  · rw [Set.indicator_of_mem hz,covariancePolynomial_mixture]
    apply Real.exp_le_exp.mpr
    have hh := (le_abs_self (μ.xi (overlap z.1 z.2))).trans (hwindow _ hz.le)
    nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β))]
  · rw [Set.indicator_of_notMem hz]
    exact (Real.exp_pos _).le

/-- A weighted overlap moment, needed for the true truncated feature
barycenter, is bounded by the same subcritical exponential estimate. -/
theorem weightedCentralOverlapMoment_eventually_bounded (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    ∃δ∈Ioo (0:ℝ) 1,∃C>0,∀ᶠ N : ℕ in atTop,
      (∫z : Vector N×Vector N,(smallOverlap δ).indicator
        (fun w => (N:ℝ)*|μ.xi (overlap w.1 w.2)| * 
          Real.exp ((N:ℝ)*β^2*μ.xi (overlap w.1 w.2))) z
          ∂(sphereLaw N).prod (sphereLaw N))≤C := by
  obtain ⟨δ,hδ,κ,hκ,hbudget,hwindow⟩ := μ.exists_subcritical_quadratic_window hβ hβs
  let b := (β^2*κ+1/2)/2
  let d := b-β^2*κ
  have hb : 0≤b := by dsimp [b]; positivity
  have hbsub : b<1/2 := by dsimp [b]; linarith
  have hd : 0<d := by dsimp [d,b]; linarith
  obtain ⟨C,hC,hbound⟩ := sphere_pair_exp_square_eventually_bounded hb hbsub
  refine ⟨δ,hδ,(κ/d)*C,mul_pos (div_pos hκ hd) hC,?_⟩
  filter_upwards [hbound,eventually_ge_atTop 1] with N hNbound hN
  have hg : Continuous (fun z : Vector N×Vector N =>
      (κ/d)*Real.exp (b*(N:ℝ)*(overlap z.1 z.2)^2)) := by unfold overlap; fun_prop
  calc
    _ ≤ ∫z : Vector N×Vector N,(κ/d)*Real.exp (b*(N:ℝ)*(overlap z.1 z.2)^2)
        ∂(sphereLaw N).prod (sphereLaw N) := by
      apply integral_mono_of_nonneg
        (.of_forall fun z => Set.indicator_nonneg (fun _ _ => by positivity) z)
        ((memLp_spherePair_continuous hN hg 1).integrable le_rfl)
      filter_upwards [] with z
      by_cases hz : z∈smallOverlap δ
      · rw [Set.indicator_of_mem hz]
        let R := overlap z.1 z.2
        let U := (N:ℝ)*R^2
        have hU : 0≤U := mul_nonneg (Nat.cast_nonneg N) (sq_nonneg R)
        have hw : |μ.xi R|≤κ*R^2 := hwindow R hz.le
        have hfirst : (N:ℝ)*|μ.xi R|≤κ*U := by
          dsimp [U]; nlinarith [mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg N)]
        have hexp : Real.exp ((N:ℝ)*β^2*μ.xi R)≤Real.exp ((β^2*κ)*U) := by
          apply Real.exp_le_exp.mpr
          have hh := (le_abs_self (μ.xi R)).trans hw
          dsimp [U]
          nlinarith [mul_le_mul_of_nonneg_left hh (mul_nonneg (Nat.cast_nonneg N) (sq_nonneg β))]
        have haux : U≤Real.exp (d*U)/d := by
          apply (le_div_iff₀ hd).mpr
          have hh := Real.add_one_le_exp (d*U)
          linarith
        calc
          _ ≤ (κ*U)*Real.exp ((β^2*κ)*U) :=
            mul_le_mul hfirst hexp (Real.exp_pos _).le (mul_nonneg hκ.le hU)
          _ ≤ (κ*(Real.exp (d*U)/d))*Real.exp ((β^2*κ)*U) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left haux hκ.le) (Real.exp_pos _).le
          _ = _ := by
            calc
              _ = (κ/d)*(Real.exp (d*U)*Real.exp ((β^2*κ)*U)) := by ring
              _ = _ := by
                rw [← Real.exp_add]
                congr 2
                dsimp [d,U,R]
                ring
      · rw [Set.indicator_of_notMem hz]
        positivity
    _ = (κ/d)*(∫z : Vector N×Vector N,Real.exp (b*(N:ℝ)*(overlap z.1 z.2)^2)
        ∂(sphereLaw N).prod (sphereLaw N)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hNbound (div_nonneg hκ.le hd.le)

end SlowEquilibration.SphericalModel
