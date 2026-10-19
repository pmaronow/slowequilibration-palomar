-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureSmoothCutoff
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceCutoff
public import SlowEquilibration.ConditionedEntrancePureOrders

/-! Dimension-independent gradient control for the literal proper-pure source
regression polynomial and its smooth cutoff. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics EntranceSmoothCutoffCalculus
open PhysicalHitting
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1600000

theorem pureRegressionCorrection_hasGradientAt {N : ℕ}
    (p : ℕ) (Q : ℝ) (u G : Vector N) (Hq e : ℝ) (x : Vector N) :
    HasGradientAt (pureRegressionCorrection p Q u G Hq e)
      (((purePrefactor Q p * (p : ℝ) * (overlap x u) ^ (p - 1) *
          ((N : ℝ) * e - Hq) -
          purePrefactor Q p * ((p - 1 : ℕ) : ℝ) *
            (overlap x u) ^ (p - 2) * inner ℝ G x) / (N : ℝ)) • u -
        pureTangentTheta Q p (overlap x u) • G) x := by
  have hR : HasFDerivAt (fun y : Vector N => overlap y u)
      ((N : ℝ)⁻¹ • innerSL ℝ u) x := by
    have hd := ((innerSL ℝ u).hasFDerivAt (x := x)).const_mul (N : ℝ)⁻¹
    convert hd using 1
    funext y
    simp only [overlap, div_eq_inv_mul]
    rw [real_inner_comm]
    rfl
  have hG := (innerSL ℝ G).hasFDerivAt (x := x)
  have h1 := ((pureValueTheta_hasDerivAt Q p (overlap x u)).comp_hasFDerivAt x hR).mul_const
    ((N : ℝ) * e - Hq)
  have h2 := ((pureTangentTheta_hasDerivAt Q p (overlap x u)).comp_hasFDerivAt x hR).mul hG
  have hd := h1.sub h2
  have hFun : pureRegressionCorrection p Q u G Hq e =
      fun y => pureValueTheta Q p (overlap y u) * ((N : ℝ) * e - Hq) -
        pureTangentTheta Q p (overlap y u) * inner ℝ G y := by
    funext y
    unfold pureRegressionCorrection pureValueTheta pureTangentTheta purePrefactor
    ring_nf
  rw [hFun]
  apply hd.congr_fderiv
  ext v
  simp only [pureTangentTheta, purePrefactor, add_apply, sub_apply,
    _root_.smul_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left,
    innerSL_apply_apply, Function.comp_apply]
  ring_nf

theorem pure_regression_uniform_orders (Q : ℝ) (p : ℕ) (r : ℝ)
    (hr : |r| ≤ 1) :
    |pureValueTheta Q p r| ≤ pureOrderConstant Q p ∧
    |pureTangentTheta Q p r| ≤ pureOrderConstant Q p ∧
    |purePrefactor Q p * (p : ℝ) * r^(p-1)| ≤ pureOrderConstant Q p ∧
    |purePrefactor Q p * ((p-1 : ℕ) : ℝ) * r^(p-2)| ≤
      pureOrderConstant Q p := by
  obtain ⟨hval,hpair,hderiv⟩ := pure_regression_orders Q p r
  have hA : 0 ≤ pureOrderConstant Q p := (pureOrderConstant_pos Q p).le
  have hpow (j : ℕ) : |r|^j ≤ 1 := pow_le_one₀ (abs_nonneg r) hr
  have hpair' :
      |purePrefactor Q p * (p : ℝ) * r^(p-1)| +
        |pureTangentTheta Q p r| ≤ pureOrderConstant Q p :=
    hpair.trans (by simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hpow (p-1)) hA)
  refine ⟨hval.trans ?_,?_,?_,hderiv.trans ?_⟩
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpow p) hA
  · linarith [abs_nonneg (purePrefactor Q p * (p : ℝ) * r^(p-1))]
  · linarith [abs_nonneg (pureTangentTheta Q p r)]
  · simpa only [mul_one] using mul_le_mul_of_nonneg_left (hpow (p-2)) hA

set_option linter.unusedVariables false in
/-- The homogeneous pure correction has dimension-independent value and
gradient constants on spherical points. The observation bounds are scalar
and will next be discharged by the original tensor regularity event. -/
theorem pure_regression_value_gradient_bounds {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (Q : ℝ) (u G x : Vector N)
    (hu : OnSphere u) (hx : OnSphere x) (Hq e B K : ℝ)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (he : |e| ≤ B)
    (hH : |Hq| ≤ K*(N : ℝ))
    (hG : ‖G‖ ≤ K*Real.sqrt (N : ℝ)) :
    |pureRegressionCorrection p Q u G Hq e x| ≤
        pureOrderConstant Q p * (B+2*K) * (N : ℝ) ∧
      ‖gradient (pureRegressionCorrection p Q u G Hq e) x‖ ≤
        pureOrderConstant Q p * (B+3*K) * Real.sqrt (N : ℝ) := by
  let A := pureOrderConstant Q p
  have hA : 0 ≤ A := (pureOrderConstant_pos Q p).le
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hxn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  have hun := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  have hr : |overlap x u| ≤ 1 := abs_le.mpr
    (overlap_mem_Icc_of_norm_sq hN x u
      ((onSphere_iff_norm_sq x).mp hx) ((onSphere_iff_norm_sq u).mp hu))
  obtain ⟨h1,h2,h3,h4⟩ := pure_regression_uniform_orders Q p (overlap x u) hr
  have hinner : |inner ℝ G x| ≤ K*(N : ℝ) := by
    calc
      _ ≤ ‖G‖*‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (K*Real.sqrt (N : ℝ))*Real.sqrt (N : ℝ) := by
        rw [hxn]
        exact mul_le_mul_of_nonneg_right hG (Real.sqrt_nonneg _)
      _ = _ := by rw [mul_assoc,Real.mul_self_sqrt hNr.le]
  have hmark : |(N : ℝ)*e-Hq| ≤ (B+K)*(N : ℝ) := by
    calc
      _ ≤ |(N : ℝ)*e|+|Hq| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le ((N : ℝ)*e) 0 Hq
      _ ≤ (N : ℝ)*B+K*(N : ℝ) := by
        rw [abs_mul,abs_of_pos hNr]
        exact add_le_add (mul_le_mul_of_nonneg_left he hNr.le) hH
      _ = _ := by ring
  have hscalar (a b : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ A) :
      |a*((N : ℝ)*e-Hq)-b*inner ℝ G x| ≤ A*(B+2*K)*(N : ℝ) := by
    calc
      _ ≤ |a*((N : ℝ)*e-Hq)|+|b*inner ℝ G x| := by
        simpa only [sub_zero,zero_sub,abs_neg] using
          abs_sub_le (a*((N : ℝ)*e-Hq)) 0 (b*inner ℝ G x)
      _ ≤ A*((B+K)*(N : ℝ))+A*(K*(N : ℝ)) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul ha hmark (abs_nonneg _) hA)
          (mul_le_mul hb hinner (abs_nonneg _) hA)
      _ = _ := by ring
  have hval := hscalar (pureValueTheta Q p (overlap x u))
    (pureTangentTheta Q p (overlap x u)) h1 h2
  have hrad := hscalar
    (purePrefactor Q p * (p : ℝ) * (overlap x u)^(p-1))
    (purePrefactor Q p * ((p-1 : ℕ) : ℝ) * (overlap x u)^(p-2)) h3 h4
  constructor
  · convert hval using 1
    unfold pureRegressionCorrection pureValueTheta pureTangentTheta purePrefactor
    ring_nf
  · rw [(pureRegressionCorrection_hasGradientAt p Q u G Hq e x).gradient]
    have hdiv :
        |(purePrefactor Q p * (p : ℝ) * (overlap x u)^(p-1) *
          ((N : ℝ)*e-Hq) -
          purePrefactor Q p * ((p-1 : ℕ) : ℝ) * (overlap x u)^(p-2) *
            inner ℝ G x)/(N : ℝ)| ≤ A*(B+2*K) := by
      rw [abs_div,abs_of_pos hNr]
      exact (div_le_iff₀ hNr).mpr hrad
    calc
      _ ≤ ‖((purePrefactor Q p * (p : ℝ) * (overlap x u)^(p-1) *
          ((N : ℝ)*e-Hq) -
          purePrefactor Q p * ((p-1 : ℕ) : ℝ) * (overlap x u)^(p-2) *
            inner ℝ G x)/(N : ℝ)) • u‖ +
          ‖pureTangentTheta Q p (overlap x u) • G‖ := norm_sub_le _ _
      _ ≤ A*(B+2*K)*Real.sqrt (N : ℝ)+A*(K*Real.sqrt (N : ℝ)) := by
        simp only [norm_smul,Real.norm_eq_abs,hun]
        exact add_le_add (mul_le_mul_of_nonneg_right hdiv (Real.sqrt_nonneg _))
          (mul_le_mul h2 hG (norm_nonneg _) hA)
      _ = _ := by dsimp [A]; ring

end SlowEquilibration.ConditionedEntrance
