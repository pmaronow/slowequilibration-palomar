-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination
public import SlowEquilibration.SphereVolume

/-!
# Arbitrary-dimensional actual round sphere chart volume

Adapted from the genuine explicit differential, determinant, and cone-Jacobian
proofs in OAI/MeasureTheory/FalconerCompletion/Sphere/SphereChartScale.lean,
Estimates/ConeJacobianMatrix.lean, and Fourier/SphereConeToLp.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (Apache-2.0).
All maps, derivatives, and Lebesgue measures here are ordinary Mathlib objects.
-/

@[expose] public section

namespace SlowEquilibration.SphereChartVolume

open Set MeasureTheory Metric Module
open scoped RealInnerProductSpace Topology ENNReal Pointwise

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

noncomputable def sphereChartScaleND (u : V) : ℝ := Real.sqrt (1-‖u‖^2/4)
noncomputable def sphereChartND (u : V) : WithLp 2 (V × ℝ) :=
  WithLp.toLp 2 (sphereChartScaleND u • u, 1-‖u‖^2/2)

omit [InnerProductSpace ℝ V] in
lemma sphereChartScaleND_pos {u : V} (hu : ‖u‖ < 2) :
    0 < sphereChartScaleND u := by
  apply Real.sqrt_pos.mpr
  nlinarith [norm_nonneg u]

omit [InnerProductSpace ℝ V] in
lemma sphereChartScaleND_sq {u : V} (hu : ‖u‖ ≤ 2) :
    sphereChartScaleND u ^ 2 = 1-‖u‖^2/4 := by
  apply Real.sq_sqrt
  nlinarith [norm_nonneg u]

lemma sphereChartND_norm {u : V} (hu : ‖u‖ ≤ 2) :
    ‖sphereChartND u‖ = 1 := by
  have hs : 0 ≤ sphereChartScaleND u := Real.sqrt_nonneg _
  have he : ‖sphereChartND u‖^2 = 1 := by
    rw [sphereChartND, WithLp.prod_norm_sq_eq_of_L2]
    change ‖sphereChartScaleND u • u‖^2 + ‖(1-‖u‖^2/2:ℝ)‖^2 = 1
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [sphereChartScaleND_sq hu]
    ring
  nlinarith [norm_nonneg (sphereChartND u)]

lemma sphereChartND_mem_sphere {u : V} (hu : ‖u‖ ≤ 2) :
    sphereChartND u ∈ sphere (0 : WithLp 2 (V × ℝ)) 1 := by
  simpa only [mem_sphere, dist_zero_right] using sphereChartND_norm hu

lemma sphereChartND_phase (u : V) :
    inner ℝ (sphereChartND u) (WithLp.toLp 2 (0, (1:ℝ))) = 1-‖u‖^2/2 := by
  simp [sphereChartND,WithLp.prod_inner_apply]

lemma sphereChartND_north : sphereChartND (0:V) = WithLp.toLp 2 (0,(1:ℝ)) := by
  simp [sphereChartND]

lemma sphereChartND_snd_gt_neg_one {u : V} (hu : ‖u‖ < 2) :
    -1 < (WithLp.ofLp (sphereChartND u)).2 := by
  change -1 < 1-‖u‖^2/2
  nlinarith [norm_nonneg u]

noncomputable def sphereChartInvND (w : WithLp 2 (V × ℝ)) : V :=
  (Real.sqrt ((1+(WithLp.ofLp w).2)/2))⁻¹ • (WithLp.ofLp w).1

lemma sphereChartND_left_inv {u : V} (hu : ‖u‖ < 2) :
    sphereChartInvND (sphereChartND u) = u := by
  have hs : sphereChartScaleND u ≠ 0 := (sphereChartScaleND_pos hu).ne'
  have he : (1+(1-‖u‖^2/2))/2 = 1-‖u‖^2/4 := by ring
  simp only [sphereChartInvND, sphereChartND, WithLp.ofLp_toLp, he]
  change (sphereChartScaleND u)⁻¹ • (sphereChartScaleND u • u) = u
  rw [← mul_smul, inv_mul_cancel₀ hs, one_smul]

lemma sphereChartND_injOn : InjOn (sphereChartND : V → WithLp 2 (V × ℝ)) (ball 0 2) := by
  intro u hu v hv he
  have hu' : ‖u‖ < 2 := by simpa using hu
  have hv' : ‖v‖ < 2 := by simpa using hv
  have := congrArg sphereChartInvND he
  simpa [sphereChartND_left_inv hu', sphereChartND_left_inv hv'] using this

lemma sphereChartInvND_norm_sq {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) :
    ‖sphereChartInvND w‖^2 = 2*(1-(WithLp.ofLp w).2) := by
  have hp : 0 < (1+(WithLp.ofLp w).2)/2 := by linarith
  have hs : Real.sqrt ((1+(WithLp.ofLp w).2)/2)^2 = (1+(WithLp.ofLp w).2)/2 :=
    Real.sq_sqrt hp.le
  have hn : ‖(WithLp.ofLp w).1‖^2 + ((WithLp.ofLp w).2)^2 = 1 := by
    have he := WithLp.prod_norm_sq_eq_of_L2 w
    rw [hw] at he
    simpa [Real.norm_eq_abs, sq_abs] using he.symm
  unfold sphereChartInvND
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, hs]
  field_simp [show 1+(WithLp.ofLp w).2 ≠ 0 by linarith]
  rw [div_eq_iff (show 1+(WithLp.ofLp w).2 ≠ 0 by linarith)]
  nlinarith [hn]

lemma sphereChartInvND_mem_ball {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) : sphereChartInvND w ∈ ball (0:V) 2 := by
  have he := sphereChartInvND_norm_sq hw ht
  rw [mem_ball, dist_zero_right]
  nlinarith [norm_nonneg (sphereChartInvND w)]

lemma sphereChartND_right_inv {w : WithLp 2 (V × ℝ)} (hw : ‖w‖ = 1)
    (ht : -1 < (WithLp.ofLp w).2) : sphereChartND (sphereChartInvND w) = w := by
  have he := sphereChartInvND_norm_sq hw ht
  have hp : 0 < (1+(WithLp.ofLp w).2)/2 := by linarith
  have hs : Real.sqrt ((1+(WithLp.ofLp w).2)/2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have hscale : sphereChartScaleND (sphereChartInvND w) =
      Real.sqrt ((1+(WithLp.ofLp w).2)/2) := by
    unfold sphereChartScaleND
    rw [he]
    congr 1
    ring
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change sphereChartScaleND (sphereChartInvND w) • sphereChartInvND w = (WithLp.ofLp w).1
    rw [hscale, sphereChartInvND, ← mul_smul, mul_inv_cancel₀ hs, one_smul]
  · change 1-‖sphereChartInvND w‖^2/2 = (WithLp.ofLp w).2
    rw [he]
    ring

lemma sphereChartScaleND_contDiffOn :
    ContDiffOn ℝ ⊤ (sphereChartScaleND : V → ℝ) (ball 0 2) := by
  apply ContDiffOn.sqrt
    ((contDiffOn_const.sub ((contDiff_norm_sq ℝ).contDiffOn.div_const 4)))
  intro u hu
  have hu' : ‖u‖ < 2 := by simpa using hu
  have : 0 < 1-‖u‖^2/4 := by nlinarith [norm_nonneg u]
  exact this.ne'

lemma sphereChartND_contDiffOn :
    ContDiffOn ℝ ⊤ (sphereChartND : V → WithLp 2 (V × ℝ)) (ball 0 2) := by
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.contDiff.comp_contDiffOn
    ((sphereChartScaleND_contDiffOn.smul contDiffOn_id).prodMk
      (contDiffOn_const.sub ((contDiff_norm_sq ℝ).contDiffOn.div_const 2)))

lemma sphereChartScaleND_hasStrictFDerivAt {u : V} (hu : ‖u‖ < 2) :
    HasStrictFDerivAt sphereChartScaleND
      ((-1/(4*sphereChartScaleND u)) • innerSL ℝ u) u := by
  have hp : 0 < 1-‖u‖^2/4 := by nlinarith [norm_nonneg u]
  have hq : HasStrictFDerivAt (fun x : V => 1-‖x‖^2/4)
      ((-(1/2:ℝ)) • innerSL ℝ u) u := by
    convert! ((hasStrictFDerivAt_norm_sq u).mul_const (1/4:ℝ)).const_sub 1 using 1
    · funext x
      ring
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
  convert! hq.sqrt hp.ne' using 1
  apply ContinuousLinearMap.ext
  intro v
  simp only [sphereChartScaleND, smul_apply, smul_eq_mul]
  ring

/-- The actual ambient derivative of the explicit sphere chart. -/
def sphereChartDerivND (u : V) : V →L[ℝ] WithLp 2 (V × ℝ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.toContinuousLinearMap.comp
    (((sphereChartScaleND u) • ContinuousLinearMap.id ℝ V +
        (((-1 / (4 * sphereChartScaleND u)) • innerSL ℝ u).smulRight u)).prod (-(innerSL ℝ u)))

lemma sphereChartND_hasStrictFDerivAt {u : V} (hu : ‖u‖ < 2) :
    HasStrictFDerivAt sphereChartND (sphereChartDerivND u) u := by
  have hs := sphereChartScaleND_hasStrictFDerivAt hu
  have hv : HasStrictFDerivAt (fun x : V => 1 - ‖x‖ ^ 2 / 2) (-(innerSL ℝ u)) u := by
    convert! ((hasStrictFDerivAt_norm_sq u).mul_const (1 / 2 : ℝ)).const_sub 1 using 1
    · funext x
      ring
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
  have hd := (WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ).symm.hasStrictFDerivAt.comp u
    ((hs.smul (hasStrictFDerivAt_id u)).prodMk hv)
  convert! hd using 1

lemma sphereChartDerivND_apply (u v : V) :
    sphereChartDerivND u v = WithLp.toLp 2
      (sphereChartScaleND u • v - (inner ℝ u v / (4 * sphereChartScaleND u)) • u,
        -inner ℝ u v) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · simp [sphereChartDerivND, sub_eq_add_neg, div_eq_mul_inv, neg_smul]
    congr 1
    ring
  · rfl

/-- The actual chart derivative is tangent to the actual unit sphere. -/
lemma sphereChartDerivND_orthogonal {u : V} (hu : ‖u‖ < 2) (v : V) :
    inner ℝ (sphereChartND u) (sphereChartDerivND u v) = 0 := by
  have hd := (hasStrictFDerivAt_norm_sq (sphereChartND u)).hasFDerivAt.comp u
    (sphereChartND_hasStrictFDerivAt hu).hasFDerivAt
  have heq : (fun x : V => ‖sphereChartND x‖ ^ 2) =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
    filter_upwards [(isOpen_ball : IsOpen (ball (0 : V) 2)).mem_nhds (by simpa using hu)] with x hx
    rw [sphereChartND_norm (le_of_lt (by simpa using hx)), one_pow]
  have hc : HasFDerivAt (fun x : V => ‖sphereChartND x‖ ^ 2) 0 u :=
    (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) u).congr_of_eventuallyEq heq
  have h := congrArg (fun L : V →L[ℝ] ℝ => L v) (hd.unique hc)
  have h' : inner ℝ (sphereChartND u) (sphereChartDerivND u v) +
      inner ℝ (sphereChartND u) (sphereChartDerivND u v) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, smul_apply, two_smul, _root_.add_apply, innerSL_apply_apply, zero_apply] using h
  linarith

noncomputable def sphereConeND (p : V × ℝ) : V × ℝ :=
  (p.2 • (sphereChartScaleND p.1 • p.1), p.2 * (1-‖p.1‖^2/2))

noncomputable def sphereConeDerivND (p : V × ℝ) : (V × ℝ) →L[ℝ] (V × ℝ) :=
  let u := p.1
  let r := p.2
  let s := sphereChartScaleND u
  let F := ContinuousLinearMap.fst ℝ V ℝ
  let T := ContinuousLinearMap.snd ℝ V ℝ
  let H := (innerSL ℝ u).comp F
  ((r*s) • F + (s • T - (r/(4*s)) • H).smulRight u).prod
    ((1-‖u‖^2/2) • T - r • H)

lemma sphereConeND_hasStrictFDerivAt {p : V × ℝ} (hp : ‖p.1‖ < 2) :
    HasStrictFDerivAt sphereConeND (sphereConeDerivND p) p := by
  have hs := (sphereChartScaleND_hasStrictFDerivAt hp).comp p hasStrictFDerivAt_fst
  have h₁ := hasStrictFDerivAt_snd.smul (hs.smul hasStrictFDerivAt_fst)
  have hv : HasStrictFDerivAt (fun x : V => 1-‖x‖^2/2) (-(innerSL ℝ p.1)) p.1 := by
    convert! ((hasStrictFDerivAt_norm_sq p.1).mul_const (1/2:ℝ)).const_sub 1 using 1
    · funext x
      ring
    · apply ContinuousLinearMap.ext
      intro v
      simp only [smul_apply, neg_apply, smul_eq_mul]
      ring
  have h₂ := (hasStrictFDerivAt_snd (𝕜 := ℝ)).mul
    (hv.comp p hasStrictFDerivAt_fst)
  convert! h₁.prodMk h₂ using 1
  apply ContinuousLinearMap.ext
  intro z
  apply Prod.ext
  · simp [sphereConeDerivND, smul_add, sub_smul, smul_smul]; module
  · simp [sphereConeDerivND]; ring

lemma sphereConeDerivND_apply (p z : V × ℝ) :
    sphereConeDerivND p z =
      ((p.2*sphereChartScaleND p.1) • z.1 +
         (sphereChartScaleND p.1*z.2-p.2/(4*sphereChartScaleND p.1)*inner ℝ p.1 z.1) • p.1,
       (1-‖p.1‖^2/2)*z.2-p.2*inner ℝ p.1 z.1) := by
  simp [sphereConeDerivND]


section
open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def coneJacobianMatrix (u : ι → ℝ) (r s : ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  let U : Matrix ι Unit ℝ := replicateCol Unit u
  let q := ∑ i, (u i)^2
  fromBlocks ((r*s) • 1 - (r/(4*s)) • (U * U.transpose))
    (s • U) ((-r) • U.transpose) ((1-q/2) • 1)

lemma coneJacobianMatrix_det (u : ι → ℝ) {r s : ℝ}
    (hr : r ≠ 0) (hs : s ≠ 0) (hsq : s^2 = 1-(∑ i, (u i)^2)/4) :
    (coneJacobianMatrix u r s).det = (r*s)^(Fintype.card ι) / s^2 := by
  let U : Matrix ι Unit ℝ := replicateCol Unit u
  let q : ℝ := ∑ i, (u i)^2
  let a : ℝ := 1-q/2
  let c : ℝ := s-a/(4*s)
  let L : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks 1 ((-1/(4*s)) • U) 0 1
  let R : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
    fromBlocks 1 ((-c/(r*s)) • U) 0 1
  have hL : L.det = 1 := by simp [L]
  have hR : R.det = 1 := by simp [R]
  have hq : U.transpose * U = q • (1 : Matrix Unit Unit ℝ) := by
    ext i j
    simp [U,q,Matrix.mul_apply, pow_two]
  have hLT : L * coneJacobianMatrix u r s =
      fromBlocks ((r*s) • (1 : Matrix ι ι ℝ)) (c • U)
        ((-r) • U.transpose) (a • (1 : Matrix Unit Unit ℝ)) := by
    change fromBlocks 1 ((-1/(4*s)) • U) 0 1 *
      fromBlocks ((r*s) • 1 - (r/(4*s)) • (U*U.transpose)) (s • U)
        ((-r) • U.transpose) (a • 1) = _
    rw [fromBlocks_multiply]
    congr 1
    · simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      have hcoef : (-r) * (-1 / (4*s)) = r/(4*s) := by ring
      rw [hcoef, sub_add_cancel]
    · simp only [Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
      rw [← add_smul]
      congr 1
      dsimp [c]
      ring
    · simp
    · simp
  have hlast : a + (-r) * (-c/(r*s)) * q = 1/s^2 := by
    dsimp [a,c]
    have he : s^2 = 1-q/4 := hsq
    field_simp
    nlinarith [he]
  have hprod : L * coneJacobianMatrix u r s * R =
      fromBlocks ((r*s) • (1 : Matrix ι ι ℝ)) (0 : Matrix ι Unit ℝ)
        ((-r) • U.transpose) ((1/s^2) • (1 : Matrix Unit Unit ℝ)) := by
    rw [hLT]
    dsimp only [R]
    rw [fromBlocks_multiply]
    congr 1
    · simp
    · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
      have hc : (-c/(r*s)) * (r*s) = -c := by field_simp
      rw [hc]
      module
    · simp
    · simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, hq]
      rw [← add_smul]
      congr 1
      linear_combination hlast
  have hd := congrArg Matrix.det hprod
  rw [det_mul, det_mul, hL, hR, one_mul, mul_one,
    det_fromBlocks_zero₁₂, det_smul, det_one, mul_one, det_smul, det_one] at hd
  simpa [div_eq_mul_inv] using hd

end

lemma sphereConeND_toLp (p : V × ℝ) :
    WithLp.toLp 2 (sphereConeND p) = p.2 • sphereChartND p.1 := rfl

lemma sphereConeND_norm {p : V × ℝ} (hp : ‖p.1‖ ≤ 2) :
    ‖WithLp.toLp 2 (sphereConeND p)‖ = |p.2| := by
  rw [sphereConeND_toLp, norm_smul, sphereChartND_norm hp, mul_one, Real.norm_eq_abs]

lemma sphereConeND_injOn : InjOn (sphereConeND : V × ℝ → V × ℝ)
    (ball 0 2 ×ˢ Ioi 0) := by
  intro p hp q hq he
  have hp' : ‖p.1‖ < 2 := by simpa using hp.1
  have hq' : ‖q.1‖ < 2 := by simpa using hq.1
  have hn := congrArg (fun z : V × ℝ => ‖WithLp.toLp 2 z‖) he
  rw [sphereConeND_norm hp'.le, sphereConeND_norm hq'.le,
    abs_of_pos hp.2, abs_of_pos hq.2] at hn
  have hc := congrArg (WithLp.toLp 2) he
  rw [sphereConeND_toLp, sphereConeND_toLp, hn] at hc
  have hu := smul_right_injective (WithLp 2 (V × ℝ)) (show q.2 ≠ 0 from ne_of_gt hq.2) hc
  exact Prod.ext (sphereChartND_injOn hp.1 hq.1 hu) hn

section Matrix
variable {n : ℕ}

noncomputable def coneBasisND (n : ℕ) :
    Basis (Fin n ⊕ Unit) ℝ (EuclideanSpace ℝ (Fin n) × ℝ) :=
  (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.prod (Basis.singleton Unit ℝ)

lemma sphereConeDerivND_toMatrix (p : EuclideanSpace ℝ (Fin n) × ℝ) :
    LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
      (sphereConeDerivND p).toLinearMap = coneJacobianMatrix p.1 p.2 (sphereChartScaleND p.1) := by
  classical
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.basisFun_apply, Matrix.mul_apply,
        PiLp.single_apply, EuclideanSpace.inner_single_right, Matrix.one_apply]
      split_ifs <;> ring
    | inr j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix]
  | inr i =>
    cases j with
    | inl j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.inner_single_right]
    | inr j =>
      simp [LinearMap.toMatrix_apply, coneBasisND, sphereConeDerivND_apply,
        coneJacobianMatrix, EuclideanSpace.real_norm_sq_eq]

lemma sphereConeDerivND_det {p : EuclideanSpace ℝ (Fin n) × ℝ}
    (hu : ‖p.1‖ < 2) (hr : p.2 ≠ 0) :
    (sphereConeDerivND p).det = (p.2*sphereChartScaleND p.1)^n / (sphereChartScaleND p.1)^2 := by
  change LinearMap.det (sphereConeDerivND p).toLinearMap = _
  rw [← LinearMap.det_toMatrix (coneBasisND n), sphereConeDerivND_toMatrix]
  have hsq : (sphereChartScaleND p.1)^2 = 1-(∑ i, (p.1 i)^2)/4 := by
    rw [sphereChartScaleND_sq hu.le]
    congr 2
    exact EuclideanSpace.real_norm_sq_eq p.1
  simpa using coneJacobianMatrix_det (fun i => p.1 i) hr (sphereChartScaleND_pos hu).ne' hsq

lemma lintegral_unitInterval_powND (n : ℕ) :
    (∫⁻ r in Ioo (0:ℝ) 1, ENNReal.ofReal (r^n)) = ((n:ℝ≥0∞)+1)⁻¹ := by
  have hi : IntegrableOn (fun r : ℝ => r^n) (Ioo 0 1) :=
    (continuous_id.pow n).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun r => r^n) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    exact pow_nonneg hr.1.le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show (0:ℝ) ≤ 1 by norm_num), integral_pow]
  simp only [one_pow, zero_pow (Nat.succ_ne_zero _), sub_zero, one_div]
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_add (by positivity) zero_le_one]
  simp

noncomputable def sphereChartWeightND (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sphereChartScaleND u ^ n / sphereChartScaleND u ^ 2

lemma sphereChartWeightND_measurable :
    Measurable (sphereChartWeightND : EuclideanSpace ℝ (Fin n) → ℝ) := by
  unfold sphereChartWeightND sphereChartScaleND
  fun_prop

lemma sphereChartWeightND_pos {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    0 < sphereChartWeightND u := by
  unfold sphereChartWeightND
  exact div_pos (pow_pos (sphereChartScaleND_pos hu) _) (sq_pos_of_pos (sphereChartScaleND_pos hu))

/-- A matrix column as the ordinary L2-product vector. -/
def coneColumnND (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ) (j : Fin n ⊕ Unit) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) :=
  WithLp.toLp 2 (WithLp.toLp 2 (fun i => A (Sum.inl i) j), A (Sum.inr ()) j)

lemma coneColumnND_inner (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℝ)
    (i j : Fin n ⊕ Unit) :
    inner ℝ (coneColumnND A i) (coneColumnND A j) = (A.transpose * A) i j := by
  simp [coneColumnND, WithLp.prod_inner_apply, PiLp.inner_apply, Matrix.mul_apply,
    Fintype.sum_sum_type, mul_comm]

lemma coneColumnND_toMatrix (u : EuclideanSpace ℝ (Fin n)) (j : Fin n ⊕ Unit) :
    coneColumnND (LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
      (sphereConeDerivND (u, 1)).toLinearMap) j =
      WithLp.toLp 2 (sphereConeDerivND (u, 1) (coneBasisND n j)) := by
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · ext i
    simp [coneColumnND, LinearMap.toMatrix_apply, coneBasisND]
  · simp [coneColumnND, LinearMap.toMatrix_apply, coneBasisND]

lemma coneColumnND_tangent (u : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    coneColumnND (LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
      (sphereConeDerivND (u, 1)).toLinearMap) (Sum.inl j) =
      sphereChartDerivND u (EuclideanSpace.basisFun (Fin n) ℝ j) := by
  rw [coneColumnND_toMatrix, sphereChartDerivND_apply]
  simp [coneBasisND, sphereConeDerivND_apply, sub_eq_add_neg, div_eq_mul_inv, neg_smul]
  congr 1
  ring

lemma coneColumnND_radial (u : EuclideanSpace ℝ (Fin n)) :
    coneColumnND (LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
      (sphereConeDerivND (u, 1)).toLinearMap) (Sum.inr ()) = sphereChartND u := by
  rw [coneColumnND_toMatrix]
  simp [coneBasisND, sphereConeDerivND_apply, sphereChartND]

/-- The actual tangent Gram matrix of the ordinary chart derivative. -/
def sphereChartGramND (u : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ (sphereChartDerivND u (EuclideanSpace.basisFun (Fin n) ℝ i))
    (sphereChartDerivND u (EuclideanSpace.basisFun (Fin n) ℝ j))

/-- The Gram matrix is the metric pullback of the actual Frechet derivative. -/
lemma sphereChartGramND_eq_fderiv {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    sphereChartGramND u = fun i j =>
      inner ℝ ((fderiv ℝ sphereChartND u) (EuclideanSpace.basisFun (Fin n) ℝ i))
        ((fderiv ℝ sphereChartND u) (EuclideanSpace.basisFun (Fin n) ℝ j)) := by
  rw [(sphereChartND_hasStrictFDerivAt hu).hasFDerivAt.fderiv]
  rfl

set_option maxHeartbeats 1000000 in
/-- The actual tangent Gram determinant is the square of the chart density. -/
theorem sphereChartGramND_det {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    (sphereChartGramND u).det = sphereChartWeightND u ^ 2 := by
  let A := LinearMap.toMatrix (coneBasisND n) (coneBasisND n)
    (sphereConeDerivND (u, 1)).toLinearMap
  have hG : A.transpose * A = Matrix.fromBlocks (sphereChartGramND u)
      (0 : Matrix (Fin n) Unit ℝ) (0 : Matrix Unit (Fin n) ℝ) 1 := by
    ext (i | i) (j | j)
    · rw [← coneColumnND_inner, coneColumnND_tangent, coneColumnND_tangent]
      rfl
    · cases j
      change (A.transpose * A) (Sum.inl i) (Sum.inr ()) = 0
      rw [← coneColumnND_inner, coneColumnND_tangent, coneColumnND_radial, real_inner_comm]
      exact sphereChartDerivND_orthogonal hu _
    · cases i
      change (A.transpose * A) (Sum.inr ()) (Sum.inl j) = 0
      rw [← coneColumnND_inner, coneColumnND_radial, coneColumnND_tangent]
      exact sphereChartDerivND_orthogonal hu _
    · cases i
      cases j
      change (A.transpose * A) (Sum.inr ()) (Sum.inr ()) = 1
      rw [← coneColumnND_inner, coneColumnND_radial, real_inner_self_eq_norm_sq,
        sphereChartND_norm hu.le, one_pow]
  have hdet : A.det = sphereChartWeightND u := by
    dsimp only [A]
    rw [LinearMap.det_toMatrix]
    simpa only [sphereChartWeightND, one_mul] using
      sphereConeDerivND_det (p := (u, 1)) hu one_ne_zero
  have hg := congrArg Matrix.det hG
  rw [Matrix.det_mul, Matrix.det_transpose, hdet, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one] at hg
  simpa only [pow_two] using hg.symm

/-- The cone-Jacobian density equals the genuine Riemannian chart volume density. -/
theorem sphereChartWeightND_eq_sqrt_gram {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    sphereChartWeightND u = Real.sqrt (sphereChartGramND u).det := by
  rw [sphereChartGramND_det hu, Real.sqrt_sq (sphereChartWeightND_pos hu).le]

lemma sphereConeND_volume {s : Set (EuclideanSpace ℝ (Fin n))} (hs : MeasurableSet s)
    (hsb : s ⊆ ball 0 2) :
    volume (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) =
      (∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u)) * ((n:ℝ≥0∞)+1)⁻¹ := by
  let : (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]
    infer_instance
  have hsub : s ×ˢ Ioo (0:ℝ) 1 ⊆ ball 0 2 ×ˢ Ioi (0:ℝ) :=
    prod_mono hsb Ioo_subset_Ioi_self
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image (volume : Measure (EuclideanSpace ℝ (Fin n) × ℝ)) (hs.prod measurableSet_Ioo)
    (f' := sphereConeDerivND)
    (fun p hp => (sphereConeND_hasStrictFDerivAt (by simpa using hsb hp.1)).hasFDerivAt.hasFDerivWithinAt)
    (sphereConeND_injOn.mono hsub)]
  have he : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => ENNReal.ofReal |(sphereConeDerivND p).det|)
      =ᵐ[volume.restrict (s ×ˢ Ioo (0:ℝ) 1)]
      (fun p => ENNReal.ofReal (sphereChartWeightND p.1) * ENNReal.ofReal (p.2^n)) := by
    filter_upwards [ae_restrict_mem (hs.prod measurableSet_Ioo)] with p hp
    have hu : ‖p.1‖ < 2 := by simpa using hsb hp.1
    rw [sphereConeDerivND_det hu hp.2.1.ne']
    have hpos : 0 ≤ (p.2*sphereChartScaleND p.1)^n / sphereChartScaleND p.1 ^ 2 := by
      exact div_nonneg (pow_nonneg (mul_nonneg hp.2.1.le (sphereChartScaleND_pos hu).le) _)
        (sq_nonneg _)
    rw [abs_of_nonneg hpos]
    rw [← ENNReal.ofReal_mul (sphereChartWeightND_pos hu).le]
    congr 1
    dsimp [sphereChartWeightND]
    rw [mul_pow]
    ring
  rw [lintegral_congr_ae he, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hf : Measurable (fun u : EuclideanSpace ℝ (Fin n) => ENNReal.ofReal (sphereChartWeightND u)) :=
    sphereChartWeightND_measurable.ennreal_ofReal
  have hg : Measurable (fun r : ℝ => ENNReal.ofReal (r^n)) := by fun_prop
  rw [lintegral_prod_mul hf.aemeasurable hg.aemeasurable, lintegral_unitInterval_powND]

lemma sphereConeND_measurableSet_image {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    MeasurableSet (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) := by
  apply (hs.prod measurableSet_Ioo).image_of_continuousOn_injOn
  · intro p hp
    exact (sphereConeND_hasStrictFDerivAt
      (by simpa using hsb hp.1)).continuousAt.continuousWithinAt
  · exact sphereConeND_injOn.mono (prod_mono hsb Ioo_subset_Ioi_self)

lemma sphereConeND_preimage_image (s : Set (EuclideanSpace ℝ (Fin n))) :
    WithLp.ofLp ⁻¹' (sphereConeND '' (s ×ˢ Ioo (0:ℝ) 1)) =
      Ioo (0:ℝ) 1 • (sphereChartND '' s) := by
  ext w
  constructor
  · rintro ⟨⟨u,r⟩, ⟨hu,hr⟩,he⟩
    refine ⟨r,hr,sphereChartND u,⟨u,hu,rfl⟩,?_⟩
    exact congrArg (WithLp.toLp 2) he
  · rintro ⟨r,hr,_,⟨u,hu,rfl⟩,he⟩
    refine ⟨(u,r),⟨hu,hr⟩,?_⟩
    exact congrArg WithLp.ofLp he

lemma sphereChartND_surface_measure {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere
      {w | (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} =
      ∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u) := by
  have hm : MeasurableSet (sphereChartND '' s) := hs.image_of_continuousOn_injOn
    (sphereChartND_contDiffOn.continuousOn.mono hsb) (sphereChartND_injOn.mono hsb)
  have himage : (Subtype.val : sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 → _) ''
      {w | (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} = sphereChartND '' s := by
    ext w
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hw
      have hsw : w ∈ sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 := by
        rcases hw with ⟨u,hu,rfl⟩
        exact sphereChartND_mem_sphere (by exact le_of_lt (by simpa using hsb hu))
      exact ⟨⟨w,hsw⟩,hw,rfl⟩
  rw [Measure.toSphere_apply' (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)))
    (show MeasurableSet {w : sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 |
      (w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) ∈ sphereChartND '' s} from
        hm.preimage measurable_subtype_coe), himage]
  have hv := (WithLp.volume_preserving_ofLp (EuclideanSpace ℝ (Fin n)) ℝ).measure_preimage
    (sphereConeND_measurableSet_image hs hsb).nullMeasurableSet
  rw [sphereConeND_preimage_image] at hv
  rw [hv, sphereConeND_volume hs hsb]
  have hd : Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) = n+1 := by
    rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod]
    simp
  rw [hd, Nat.cast_add, Nat.cast_one]
  rw [mul_comm _ ((∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u)) * _), mul_assoc,
    ENNReal.inv_mul_cancel (by positivity) (by finiteness), mul_one]

lemma sphereChartND_continuous :
    Continuous (sphereChartND : EuclideanSpace ℝ (Fin n) → _) := by
  unfold sphereChartND sphereChartScaleND
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) ℝ).symm.continuous.comp
    (by fun_prop)

noncomputable def sphereAreaND (n : ℕ) : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  Measure.map Subtype.val (volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere

lemma sphereAreaND_chart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    sphereAreaND n (sphereChartND '' s) = ∫⁻ u in s, ENNReal.ofReal (sphereChartWeightND u) := by
  rw [sphereAreaND, Measure.map_apply measurable_subtype_coe
    (hs.image_of_continuousOn_injOn sphereChartND_continuous.continuousOn (sphereChartND_injOn.mono hsb))]
  exact sphereChartND_surface_measure hs hsb

lemma sphereAreaND_restrict_chart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (sphereAreaND n).restrict (sphereChartND '' s) =
      Measure.map sphereChartND ((volume.restrict s).withDensity (fun u => ENNReal.ofReal (sphereChartWeightND u))) := by
  ext t ht
  rw [Measure.restrict_apply ht, Measure.map_apply sphereChartND_continuous.measurable ht,
    withDensity_apply _ (sphereChartND_continuous.measurable ht),
    Measure.restrict_restrict (sphereChartND_continuous.measurable ht)]
  have hset : t ∩ sphereChartND '' s = sphereChartND '' (sphereChartND ⁻¹' t ∩ s) := by
    ext w
    simp only [mem_inter_iff, mem_image, mem_preimage]
    constructor
    · rintro ⟨hw, u, hu, rfl⟩
      exact ⟨u,⟨hw,hu⟩,rfl⟩
    · rintro ⟨u,⟨hu,hsu⟩,rfl⟩
      exact ⟨hu,u,hsu,rfl⟩
  rw [hset, sphereAreaND_chart ((sphereChartND_continuous.measurable ht).inter hs)
    (inter_subset_right.trans hsb)]


/-- The ordinary unit sphere chart covers precisely the sphere above its omitted pole. -/
lemma sphereChartND_image_ball :
    sphereChartND '' (ball (0 : EuclideanSpace ℝ (Fin n)) 2) =
      {w : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) | ‖w‖ = 1 ∧ -1 < (WithLp.ofLp w).2} := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hu' : ‖u‖ < 2 := by simpa using hu
    exact ⟨sphereChartND_norm hu'.le, sphereChartND_snd_gt_neg_one hu'⟩
  · intro hw
    exact ⟨sphereChartInvND w, sphereChartInvND_mem_ball hw.1 hw.2,
      sphereChartND_right_inv hw.1 hw.2⟩

/-- Two genuine ordinary round charts cover the entire unit sphere. -/
theorem sphereChartND_two_charts_cover :
    sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) 1 =
      sphereChartND '' (ball (0 : EuclideanSpace ℝ (Fin n)) 2) ∪
        (fun u => -sphereChartND u) '' (ball (0 : EuclideanSpace ℝ (Fin n)) 2) := by
  ext w
  constructor
  · intro hw
    have hn : ‖w‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hw
    by_cases ht : -1 < (WithLp.ofLp w).2
    · exact Or.inl (sphereChartND_image_ball ▸ ⟨hn, ht⟩)
    · apply Or.inr
      have hn' : ‖-w‖ = 1 := by simpa using hn
      have ht' : -1 < (WithLp.ofLp (-w)).2 := by
        change -1 < -(WithLp.ofLp w).2
        linarith
      have hm : -w ∈ sphereChartND '' (ball (0 : EuclideanSpace ℝ (Fin n)) 2) := by
        rw [sphereChartND_image_ball]
        exact ⟨hn', ht'⟩
      obtain ⟨u, hu, he⟩ := hm
      exact ⟨u, hu, by change -sphereChartND u = w; rw [he, neg_neg]⟩
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩) <;>
      simpa only [mem_sphere, dist_zero_right, norm_neg] using
        sphereChartND_norm (le_of_lt (by simpa using hu))

/-- The actual ambient normalized angular law. -/
def normalizedSphereAreaND (n : ℕ) : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) :=
  ((volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere univ)⁻¹ • sphereAreaND n

lemma normalizedSphereAreaND_eq_angular : normalizedSphereAreaND n =
    (SphereVolume.unitAngular (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).map Subtype.val := by
  rw [SphereVolume.unitAngular, Measure.map_smul _ measurable_subtype_coe.aemeasurable]
  rfl

/-- Genuine normalized round chart law, with the actual Riemannian tangent Gram density. -/
theorem normalizedSphereAreaND_restrict_chart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (normalizedSphereAreaND n).restrict (sphereChartND '' s) =
      ((volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere univ)⁻¹ •
        Measure.map sphereChartND ((volume.restrict s).withDensity
          (fun u => ENNReal.ofReal (Real.sqrt (sphereChartGramND u).det))) := by
  rw [normalizedSphereAreaND, Measure.restrict_smul, sphereAreaND_restrict_chart hs hsb]
  congr 2
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hs] with u hu
  rw [sphereChartWeightND_eq_sqrt_gram (by simpa using hsb hu)]

lemma chartAmbient_finrank (n : ℕ) :
    Module.finrank ℝ (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) = n + 1 := by
  rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod]
  simp

/-- An ordinary linear isometry identifies the round chart ambient space with
the manuscript's actual Euclidean vector space. -/
def chartAmbientIsometry (n : ℕ) :
    WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) ≃ₗᵢ[ℝ] SphericalAging.FiniteModel.Vector (n + 1) :=
  ((stdOrthonormalBasis ℝ (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).reindex
    (finCongr (chartAmbient_finrank n))).repr

/-- The ordinary round chart at the manuscript's true radius `sqrt(n+1)`. -/
def manuscriptChart (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) : SphericalAging.FiniteModel.Vector (n + 1) :=
  Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n (sphereChartND u)

/-- The true derivative of the actual-radius manuscript chart. -/
def manuscriptChartDerivative (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] SphericalAging.FiniteModel.Vector (n + 1) :=
  (Real.sqrt (n + 1 : ℕ)) •
    (chartAmbientIsometry n).toContinuousLinearEquiv.toContinuousLinearMap.comp (sphereChartDerivND u)

lemma manuscriptChart_hasFDerivAt {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    HasFDerivAt (manuscriptChart n) (manuscriptChartDerivative n u) u := by
  have hd := ((chartAmbientIsometry n).toContinuousLinearEquiv.hasFDerivAt.comp u
    (sphereChartND_hasStrictFDerivAt hu).hasFDerivAt).const_smul (Real.sqrt (n + 1 : ℕ))
  convert! hd using 1

/-- The actual pullback of the manuscript sphere's ordinary round metric. -/
def manuscriptChartGram (n : ℕ) (u : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => inner ℝ ((fderiv ℝ (manuscriptChart n) u) (EuclideanSpace.basisFun (Fin n) ℝ i))
    ((fderiv ℝ (manuscriptChart n) u) (EuclideanSpace.basisFun (Fin n) ℝ j))

lemma manuscriptChartGram_eq_scaled {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    manuscriptChartGram n u = (Real.sqrt (n + 1 : ℕ)) ^ 2 • sphereChartGramND u := by
  unfold manuscriptChartGram
  rw [(manuscriptChart_hasFDerivAt hu).fderiv]
  ext i j
  simp only [manuscriptChartDerivative, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    inner_smul_left, inner_smul_right, conj_trivial,
    LinearIsometryEquiv.inner_map_map, sphereChartGramND, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Radius scaling of the actual round Riemannian chart density. -/
theorem manuscriptChart_riemannian_density {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    Real.sqrt (manuscriptChartGram n u).det =
      (Real.sqrt (n + 1 : ℕ)) ^ n * sphereChartWeightND u := by
  have hd : (manuscriptChartGram n u).det =
      ((Real.sqrt (n + 1 : ℕ)) ^ n * sphereChartWeightND u) ^ 2 := by
    rw [manuscriptChartGram_eq_scaled hu, Matrix.det_smul, sphereChartGramND_det hu]
    simp only [Fintype.card_fin, mul_pow, ← pow_mul]
    rw [Nat.mul_comm n 2]
  rw [hd, Real.sqrt_sq (mul_nonneg (pow_nonneg (Real.sqrt_nonneg _) _) (sphereChartWeightND_pos hu).le)]

lemma sphereLaw_eq_normalizedSphereAreaND (n : ℕ) :
    SphericalAging.SphereInitialLaw.sphereLaw (n + 1) =
      (normalizedSphereAreaND n).map
        (fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w) := by
  let e := chartAmbientIsometry n
  have hm : Measurable (SphereVolume.normalize (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
      (Real.sqrt (n + 1 : ℕ))) := by unfold SphereVolume.normalize; fun_prop
  have heq : e ∘ SphereVolume.normalize (Real.sqrt (n + 1 : ℕ)) =
      SphericalAging.SphereInitialLaw.normalize (n + 1) ∘ e := by
    funext w
    simp [SphereVolume.normalize, SphericalAging.SphereInitialLaw.normalize]
  rw [normalizedSphereAreaND_eq_angular, Measure.map_map (by fun_prop) measurable_subtype_coe]
  have hn := SphereVolume.normalizedGaussian_eq_angular
    (E := WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ)) (Real.sqrt (n + 1 : ℕ))
  have hmap := congrArg (fun μ => μ.map e) hn
  rw [Measure.map_map e.continuous.measurable hm, heq,
    ← Measure.map_map (SphericalAging.SphereInitialLaw.normalize_measurable (n + 1))
      e.continuous.measurable, ProbabilityTheory.stdGaussian_map e] at hmap
  rw [Measure.map_map e.continuous.measurable (by fun_prop)] at hmap
  simpa only [Function.comp_def, map_smul, e, SphericalAging.SphereInitialLaw.sphereLaw,
    SphericalAging.SphereInitialLaw.gaussianLaw] using hmap

/-- The manuscript's actual sphere law has the normalized ordinary round
Riemannian chart density on every Borel region of this genuine chart. -/
theorem sphereLaw_restrict_manuscriptChart {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : MeasurableSet s) (hsb : s ⊆ ball 0 2) :
    (SphericalAging.SphereInitialLaw.sphereLaw (n + 1)).restrict (manuscriptChart n '' s) =
      ((volume : Measure (WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))).toSphere univ)⁻¹ •
        Measure.map (manuscriptChart n) ((volume.restrict s).withDensity
          (fun u => ENNReal.ofReal (Real.sqrt (sphereChartGramND u).det))) := by
  let f : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ) → SphericalAging.FiniteModel.Vector (n + 1) :=
    fun w => Real.sqrt (n + 1 : ℕ) • chartAmbientIsometry n w
  have hpos : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (by positivity)
  have hf : MeasurableEmbedding f :=
    ((chartAmbientIsometry n).toHomeomorph.trans (Homeomorph.smulOfNeZero (Real.sqrt (n + 1 : ℕ)) hpos.ne')).measurableEmbedding
  have hset : manuscriptChart n '' s = f '' (sphereChartND '' s) := by
    rw [← image_comp]
    rfl
  rw [sphereLaw_eq_normalizedSphereAreaND, hset, hf.restrict_map,
    preimage_image_eq _ hf.injective, normalizedSphereAreaND_restrict_chart hs hsb,
    Measure.map_smul _ hf.measurable.aemeasurable,
    Measure.map_map hf.measurable sphereChartND_continuous.measurable]
  rfl

/-- The genuine chart density is continuous on its entire smooth chart domain. -/
lemma sphereChartWeightND_continuousOn :
    ContinuousOn (sphereChartWeightND : EuclideanSpace ℝ (Fin n) → ℝ) (ball 0 2) := by
  apply (sphereChartScaleND_contDiffOn.continuousOn.pow n).div
    (sphereChartScaleND_contDiffOn.continuousOn.pow 2)
  intro u hu
  exact pow_ne_zero 2 (sphereChartScaleND_pos (by simpa using hu)).ne'

/-- Explicit positive lower and finite upper bounds on the larger compact
chart region used for cutoffs around the two-chart covering. -/
theorem sphereChartWeightND_closedBall_bounds {u : EuclideanSpace ℝ (Fin n)}
    (hu : u ∈ closedBall 0 (Real.sqrt 3)) :
    (1 / 2 : ℝ) ^ n ≤ sphereChartWeightND u ∧ sphereChartWeightND u ≤ 4 := by
  have hun : ‖u‖ ≤ Real.sqrt 3 := by simpa only [mem_closedBall, dist_zero_right] using hu
  have hu3 : ‖u‖ ^ 2 ≤ 3 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), norm_nonneg u]
  have hu2 : ‖u‖ < 2 := by nlinarith [norm_nonneg u]
  have hs := sphereChartScaleND_sq hu2.le
  have hsp := sphereChartScaleND_pos hu2
  have hslo : (1 / 2 : ℝ) ≤ sphereChartScaleND u := by nlinarith
  have hshi : sphereChartScaleND u ≤ 1 := by nlinarith [sq_nonneg ‖u‖]
  have hden : 0 < sphereChartScaleND u ^ 2 := sq_pos_of_pos hsp
  unfold sphereChartWeightND
  constructor
  · apply (le_div_iff₀ hden).2
    calc
      (1 / 2 : ℝ) ^ n * sphereChartScaleND u ^ 2 ≤ (1 / 2 : ℝ) ^ n * 1 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      _ ≤ sphereChartScaleND u ^ n := by
        simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hslo n
  · apply (div_le_iff₀ hden).2
    have hp : sphereChartScaleND u ^ n ≤ 1 := pow_le_one₀ hsp.le hshi
    nlinarith

/-- A closed chart region on either side, of radius `sqrt 2`, covers every
point of the actual manuscript sphere; the larger `sqrt 3` region provides cutoff margin. -/
theorem manuscriptChart_two_closed_charts_cover :
    sphere (0 : SphericalAging.FiniteModel.Vector (n + 1)) (Real.sqrt (n + 1 : ℕ)) =
      manuscriptChart n '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt 2) ∪
        (fun u => -manuscriptChart n u) '' closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt 2) := by
  let R : ℝ := Real.sqrt (n + 1 : ℕ)
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  ext x
  constructor
  · intro hx
    have hxn : ‖x‖ = R := by simpa only [mem_sphere, dist_zero_right] using hx
    let w := (chartAmbientIsometry n).symm (R⁻¹ • x)
    have hwn : ‖w‖ = 1 := by
      simp only [w, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hR), hxn]
      exact inv_mul_cancel₀ hR.ne'
    have hxw : R • chartAmbientIsometry n w = x := by
      rw [show chartAmbientIsometry n w = R⁻¹ • x from (chartAmbientIsometry n).apply_symm_apply _,
        smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
    have hpoint (v : WithLp 2 (EuclideanSpace ℝ (Fin n) × ℝ))
        (hv : ‖v‖ = 1) (ht : 0 ≤ (WithLp.ofLp v).2) :
        ∃ u ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) (Real.sqrt 2), sphereChartND u = v := by
      have ht' : -1 < (WithLp.ofLp v).2 := by linarith
      have hi := sphereChartInvND_norm_sq hv ht'
      refine ⟨sphereChartInvND v, ?_, sphereChartND_right_inv hv ht'⟩
      rw [mem_closedBall, dist_zero_right]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), norm_nonneg (sphereChartInvND v),
        Real.sqrt_nonneg (2 : ℝ)]
    by_cases ht : 0 ≤ (WithLp.ofLp w).2
    · obtain ⟨u, hu, he⟩ := hpoint w hwn ht
      exact Or.inl ⟨u, hu, by rw [manuscriptChart, he]; exact hxw⟩
    · have ht' : 0 ≤ (WithLp.ofLp (-w)).2 := by
        change 0 ≤ -(WithLp.ofLp w).2
        linarith
      obtain ⟨u, hu, he⟩ := hpoint (-w) (by simpa using hwn) ht'
      apply Or.inr
      refine ⟨u, hu, ?_⟩
      change -(R • chartAmbientIsometry n (sphereChartND u)) = x
      rw [he, map_neg, smul_neg, neg_neg]
      exact hxw
  · rintro (⟨u, hu, rfl⟩ | ⟨u, hu, rfl⟩)
    all_goals
      have hu' : ‖u‖ ≤ Real.sqrt 2 := by simpa only [mem_closedBall, dist_zero_right] using hu
      have hu2 : ‖u‖ ≤ 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), norm_nonneg u]
      simp only [mem_sphere, dist_zero_right, norm_neg, manuscriptChart,
        norm_smul, LinearIsometryEquiv.norm_map, sphereChartND_norm hu2, mul_one,
        Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

end Matrix

end
end SlowEquilibration.SphereChartVolume
