module

public import SphericalAging.HessianSourceDifference

public section
/-! L² continuity bounds for literal Hessian sources from mixed moments. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HessianSourceNorm
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FirstVariationDifferenceLpBounds LpThreeProductBounds
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem source_difference_norm_le (D : BrownianDriver N P F) {Kb Ks L M : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hbg : ∀ i,ContDiff ℝ ∞ (b i)) (hsg : ∀ i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A)
    (x y : State N) (T : ℝ≥0) (g : State N → ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g)) (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (v w : State N)
    (hi4 : MemLp (stateTimeCut (increment D hb hs x y T) T) 4 (nonnegativeLebesgueMeasure.prod P))
    (hv8 : MemLp (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hw8 : MemLp (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hdv4 : MemLp (differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P))
    (hdw4 : MemLp (differenceCut D hbg hsg hb hs x y T w) 4 (nonnegativeLebesgueMeasure.prod P)) :
    ‖HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL v w-
      HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w‖≤
      (M : ℝ)*lpNorm (stateTimeCut (increment D hb hs x y T) T) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 8 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 (nonnegativeLebesgueMeasure.prod P)+
      (L : ℝ)*lpNorm (differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 4 (nonnegativeLebesgueMeasure.prod P)+
      (L : ℝ)*lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T) 4 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (differenceCut D hbg hsg hb hs x y T w) 4 (nonnegativeLebesgueMeasure.prod P) := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let I := stateTimeCut (increment D hb hs x y T) T
  let V := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T
  let W := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T
  let X := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T
  let DV := differenceCut D hbg hsg hb hs x y T v
  let DW := differenceCut D hbg hsg hb hs x y T w
  let R := HessianInitialSource.source D hbg hsg hb hs hnull y T g hg hL v w-
    HessianInitialSource.source D hbg hsg hb hs hnull x T g hg hL v w
  let A : ℝ≥0 × Ω → ℝ := (M : ℝ) • (fun q => ‖I q‖*‖V q‖*‖W q‖)
  let B : ℝ≥0 × Ω → ℝ := (L : ℝ) • (fun q => ‖DV q‖*‖W q‖)
  let C : ℝ≥0 × Ω → ℝ := (L : ℝ) • (fun q => ‖X q‖*‖DW q‖)
  have hW4 := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs y T hnull w).1
  have hX4 := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull v).1
  have hVW : MemLp (fun q => ‖V q‖*‖W q‖) 4 μ := hv8.norm.fun_mul hw8.norm
  have hA : MemLp A 2 μ := by
    simpa only [A,Pi.smul_apply,smul_eq_mul,mul_assoc] using
      (hi4.norm.fun_mul hVW).const_smul (M : ℝ)
  have hB : MemLp B 2 μ := (hdv4.norm.fun_mul hW4.norm).const_smul (L : ℝ)
  have hC : MemLp C 2 μ := (hX4.norm.fun_mul hdw4.norm).const_smul (L : ℝ)
  have hn := lpNorm_dominated_sum_le (R : TimeProcessL2 P) A B C (Lp.memLp _) hA hB hC
    (fun q => by dsimp [A,B,C];positivity)
    (by simpa only [A,B,C,Pi.smul_apply,smul_eq_mul,mul_assoc] using
      HessianSourceDifference.source_difference_bound D hbg hsg hb hs hnull x y T g hg hL v w hM)
  have hAn : lpNorm A 2 μ≤(M : ℝ)*lpNorm I 4 μ*lpNorm V 8 μ*lpNorm W 8 μ := by
    dsimp only [A]
    rw [lpNorm_const_smul,coe_nnnorm,Real.norm_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hi4 hv8 hw8) M.coe_nonneg
  have hBn : lpNorm B 2 μ≤(L : ℝ)*lpNorm DV 4 μ*lpNorm W 4 μ := by
    dsimp only [B]
    rw [lpNorm_const_smul,coe_nnnorm,Real.norm_of_nonneg L.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (LpProductBounds.lpNorm_product_le hdv4 hW4) L.coe_nonneg
  have hCn : lpNorm C 2 μ≤(L : ℝ)*lpNorm X 4 μ*lpNorm DW 4 μ := by
    dsimp only [C]
    rw [lpNorm_const_smul,coe_nnnorm,Real.norm_of_nonneg L.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (LpProductBounds.lpNorm_product_le hX4 hdw4) L.coe_nonneg
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  exact hn.trans (add_le_add (add_le_add hAn hBn) hCn)
end SphericalAging.HessianSourceNorm
