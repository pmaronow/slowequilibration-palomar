-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureGradientBound

/-! A dimension-independent gradient bound for the literal proper-pure
cutoff Hamiltonian on the original tensor regularity event. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory Set SphericalModel SphericalForm SphericalGaussianJet
open SphericalAging HardSphereDynamics EntranceSmoothCutoffCalculus
open PhysicalHitting SphericalSmoothTensorStationarity
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem regular_pure_center_observations {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (u : Vector N) (hu : OnSphere u) :
    let μ := FiniteMixture.pure p hp c hc
    let cQ := centerCoefficients (mixtureCoefficients μ) Q
    |field cQ J u| ≤ centerConstant μ Q*(N : ℝ) ∧
      ‖surfaceGradient (field cQ J) u‖ ≤ centerConstant μ Q*Real.sqrt (N : ℝ) := by
  dsimp only
  have hun := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  have hb := field_regularDisorder_ball_bounds hN
    (centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q)
    J hJ u hun.le
  refine ⟨hb.1,?_⟩
  unfold surfaceGradient
  have hproj := projection_norm_le_onSphere (by omega : N ≠ 0) u
    (gradient (field (centerCoefficients
      (mixtureCoefficients (FiniteMixture.pure p hp c hc)) Q) J) u) hu
  simpa only [tangentProjection_apply,centerConstant] using hproj.trans hb.2.1

def pureSourceGradientConstant (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q B α : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) : ℝ :=
  let μ := FiniteMixture.pure p hp c hc
  let K := centerConstant μ Q
  let A := pureOrderConstant Q p
  derivativeConstant (mixtureCoefficients μ) +
    (scalarCutoffConstant χ hχ (sourceArgumentRadius μ Q α))^2 *
      (A*(B+2*K)*(1+K)/α+A*(B+3*K))

theorem pureSourceGradientConstant_nonneg (p : ℕ) (hp : 2 ≤ p)
    (c : ℝ) (hc : 0 < c) (Q B : ℝ) (hB : 0 ≤ B)
    {α : ℝ} (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    0 ≤ pureSourceGradientConstant p hp c hc Q B α χ hχ := by
  unfold pureSourceGradientConstant
  have := (derivativeConstant_pos (mixtureCoefficients (FiniteMixture.pure p hp c hc))).le
  have := (centerConstant_pos (FiniteMixture.pure p hp c hc) Q).le
  have := (pureOrderConstant_pos Q p).le
  positivity

/-- The constant is chosen before dimension, disorder, axis and every
value mark in the prescribed bounded interval. No cutoff derivative or
gradient bound is an external premise. -/
theorem regular_pure_source_gradient_bound {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c) (Q B : ℝ)
    (hB : 0 ≤ B) {α : ℝ} (hα : 0 < α)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (J : Disorder N (FiniteMixture.pure p hp c hc).maxDegree)
    (hJ : J ∈ regularDisorder) (u : Vector N) (hu : OnSphere u)
    (e : ℝ) (he : |e| ≤ B) (x : Vector N) (hx : OnSphere x) :
    ‖gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) x‖ ≤
      pureSourceGradientConstant p hp c hc Q B α χ hχ * Real.sqrt (N : ℝ) := by
  let μ := FiniteMixture.pure p hp c hc
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let G := surfaceGradient (field cQ J) u
  let F := pureRegressionCorrection p Q u G (field cQ J u) e
  let v1 := ((N : ℝ)*α)⁻¹ • u
  let v2 := ((N : ℝ)*α)⁻¹ • G
  let A := pureOrderConstant Q p
  let K := centerConstant μ Q
  let R := sourceArgumentRadius μ Q α
  let L := scalarCutoffConstant χ hχ R
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hK : 0 ≤ K := (centerConstant_pos μ Q).le
  have hA : 0 ≤ A := (pureOrderConstant_pos Q p).le
  have hL : 0 ≤ L := scalarCutoffConstant_nonneg χ hχ R
  have hxn := LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  have hun := LandscapeDerivatives.sphere_norm u ((onSphere_iff_norm_sq u).mp hu)
  obtain ⟨hH,hG⟩ := regular_pure_center_observations hN p hp c hc Q J hJ u hu
  change |field cQ J u| ≤ K*(N : ℝ) at hH
  change ‖G‖ ≤ K*Real.sqrt (N : ℝ) at hG
  have hv1 : ‖v1‖ = ((N : ℝ)*α)⁻¹*Real.sqrt (N : ℝ) := by
    simp only [v1,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le)),hun]
  have hv2 : ‖v2‖ ≤ ((N : ℝ)*α)⁻¹*K*Real.sqrt (N : ℝ) := by
    simp only [v2,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (mul_nonneg hNr.le hα.le))]
    exact (mul_le_mul_of_nonneg_left hG
      (inv_nonneg.mpr (mul_nonneg hNr.le hα.le))).trans_eq (by ring)
  have harg1 : |inner ℝ v1 x| ≤ 1/α := by
    calc
      _ ≤ ‖v1‖*‖x‖ := abs_real_inner_le_norm _ _
      _ = 1/α := by
        rw [hv1,hxn,mul_assoc,Real.mul_self_sqrt hNr.le]
        field_simp
  have harg2 : |inner ℝ v2 x| ≤ K/α := by
    calc
      _ ≤ ‖v2‖*‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ (((N : ℝ)*α)⁻¹*K*Real.sqrt (N : ℝ))*Real.sqrt (N : ℝ) := by
        rw [hxn]
        exact mul_le_mul_of_nonneg_right hv2 (Real.sqrt_nonneg _)
      _ = K/α := by
        rw [mul_assoc,Real.mul_self_sqrt hNr.le]
        field_simp
  have hr1 : inner ℝ v1 x ∈ Icc (-R) R := by
    apply abs_le.mp
    apply harg1.trans
    change 1/α ≤ 1+(1+K)/α
    rw [add_div]
    linarith [div_nonneg hK hα.le]
  have hr2 : inner ℝ v2 x ∈ Icc (-R) R := by
    apply abs_le.mp
    apply harg2.trans
    change K/α ≤ 1+(1+K)/α
    rw [add_div]
    linarith [one_div_pos.mpr hα]
  obtain ⟨h1,hd1⟩ := scalarCutoffConstant_bounds χ hχ R (inner ℝ v1 x) hr1
  obtain ⟨h2,hd2⟩ := scalarCutoffConstant_bounds χ hχ R (inner ℝ v2 x) hr2
  obtain ⟨hval,hgrad⟩ := pure_regression_value_gradient_bounds hN p Q u G x hu hx
    (field cQ J u) e B K hB hK he hH hG
  change |F x| ≤ A*(B+2*K)*(N : ℝ) at hval
  change ‖gradient F x‖ ≤ A*(B+3*K)*Real.sqrt (N : ℝ) at hgrad
  have hF : Differentiable ℝ F := fun y =>
    (pureRegressionCorrection_hasGradientAt p Q u G (field cQ J u) e y).differentiableAt
  have hcor := cutoffCorrection_gradient_norm_le χ
    (hχ.differentiable (by norm_num)) v1 v2 F x (hF x)
    hL h1 h2 hd1 hd2 hval hgrad
  have hvs : ‖v1‖+‖v2‖ ≤ ((N : ℝ)*α)⁻¹*(1+K)*Real.sqrt (N : ℝ) :=
    (add_le_add hv1.le hv2).trans_eq (by ring)
  have hcorr : ‖gradient (cutoffCorrection χ χ v1 v2 F) x‖ ≤
      L^2*(A*(B+2*K)*(1+K)/α+A*(B+3*K))*Real.sqrt (N : ℝ) := by
    apply hcor.trans
    calc
      _ ≤ L^2*((A*(B+2*K)*(N : ℝ))*
          (((N : ℝ)*α)⁻¹*(1+K)*Real.sqrt (N : ℝ))+
          A*(B+3*K)*Real.sqrt (N : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        exact add_le_add (mul_le_mul_of_nonneg_left hvs (by positivity)) le_rfl
      _ = _ := by field_simp
  have hamiltonian : pureSourceSmoothCutoffField p hp c hc Q J u e α χ =
      fun y => fieldOfMixture μ J y+cutoffCorrection χ χ v1 v2 F y := by
    funext y
    have hr : inner ℝ v1 y = overlap y u/α := by
      dsimp only [v1]
      rw [real_inner_smul_left,real_inner_comm y u]
      unfold overlap
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    have hs : inner ℝ v2 y = inner ℝ G y/((N : ℝ)*α) := by
      dsimp only [v2]
      rw [real_inner_smul_left]
      exact (div_eq_inv_mul _ _).symm
    change fieldOfMixture μ J y+
      χ (overlap y u/α)*χ (inner ℝ G y/((N : ℝ)*α))*F y =
      fieldOfMixture μ J y+χ (inner ℝ v1 y)*χ (inner ℝ v2 y)*F y
    rw [hr,hs]
  have hbase := (fieldOfMixture_contDiff μ J).differentiable (by simp)
  have hcut := cutoffCorrection_hasGradientAt χ χ v1 v2 F x
    ((hχ.differentiable (by norm_num)) _) ((hχ.differentiable (by norm_num)) _) (hF x)
  have hfull : gradient (pureSourceSmoothCutoffField p hp c hc Q J u e α χ) x =
      gradient (fieldOfMixture μ J) x+gradient (cutoffCorrection χ χ v1 v2 F) x := by
    rw [hamiltonian]
    exact ((hbase x).hasFDerivAt.add hcut.differentiableAt.hasFDerivAt).hasGradientAt.gradient.trans
      ((InnerProductSpace.toDual ℝ (Vector N)).symm.map_add _ _)
  have hbaseBound := (field_regularDisorder_ball_bounds hN
    (mixtureCoefficients μ) J hJ x hxn.le).2.1
  rw [hfull]
  exact (norm_add_le _ _).trans ((add_le_add hbaseBound hcorr).trans_eq (by
    dsimp only [pureSourceGradientConstant,L,R,A,K,μ]
    ring))

end SlowEquilibration.ConditionedEntrance
