-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureCurvature
public import SlowEquilibration.SphericalGaussianJet

/-! A genuine finite covariance for the original field restricted to a
radius-`sqrt(N*q)` center sphere. Its coefficient at degree `p` is
`μ.coeff p * q^p`; the support and maximum degree are unchanged for `q>0`. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundStateRadialCoefficients

open SphericalModel SphericalGaussianJet
set_option autoImplicit false

/-- Radial covariance polynomial `ξ_q(t)=ξ(qt)` as a canonical nonzero
finite mixture. -/
def centerMixture (μ : FiniteMixture) (q : ℝ) (hq : 0 < q) : FiniteMixture where
  coeff := Finsupp.onFinset μ.coeff.support (fun p => μ.coeff p * q ^ p) (by
    intro p hp
    by_contra hnot
    have hzero : μ.coeff p = 0 := by
      by_contra h
      exact hnot (Finsupp.mem_support_iff.mpr h)
    exact hp (by simp [hzero]))
  nonneg := by
    intro p
    rw [Finsupp.onFinset_apply]
    exact mul_nonneg (μ.nonneg p) (pow_nonneg hq.le _)
  zero_below_two := by
    intro p hp
    rw [Finsupp.onFinset_apply, μ.zero_below_two p hp, zero_mul]
  nonzero := by
    obtain ⟨p, hp⟩ := μ.support_nonempty
    intro hz
    have hz' := congrArg (fun f : ℕ →₀ ℝ => f p) hz
    rw [Finsupp.onFinset_apply] at hz'
    simp only [Finsupp.zero_apply] at hz'
    exact (mul_ne_zero (μ.coeff_pos hp).ne' (pow_ne_zero p hq.ne')) hz'

@[simp] theorem centerMixture_coeff (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) (p : ℕ) :
    (centerMixture μ q hq).coeff p = μ.coeff p * q ^ p :=
  rfl

theorem centerMixture_support (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) :
    (centerMixture μ q hq).coeff.support = μ.coeff.support := by
  ext p
  rw [Finsupp.mem_support_iff, centerMixture_coeff,
    Finsupp.mem_support_iff, mul_ne_zero_iff]
  simp [pow_ne_zero p hq.ne']

theorem centerMixture_maxDegree (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) :
    (centerMixture μ q hq).maxDegree = μ.maxDegree := by
  unfold FiniteMixture.maxDegree
  congr 1
  exact centerMixture_support μ q hq

theorem centerMixture_xi (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) (t : ℝ) :
    (centerMixture μ q hq).xi t = μ.xi (q * t) := by
  unfold FiniteMixture.xi
  rw [centerMixture_support]
  apply Finset.sum_congr rfl
  intro p hp
  rw [centerMixture_coeff, mul_pow]
  ring

/-- On the original degree-index type, the new canonical coefficients are
literally those of the center field `H_N(sqrt(q)·)`. -/
theorem centerMixture_coefficients (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) :
    (fun p : Degree μ.maxDegree => (centerMixture μ q hq).coeff p.val.val) =
      centerCoefficients (mixtureCoefficients μ) q := by
  funext p
  simp [centerMixture_coeff, centerCoefficients, mixtureCoefficients]

/-- Thus the original center field and the scaled-mixture field agree
sample by sample under the same original ordered Gaussian tensors. -/
theorem centerMixture_field (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) {N : ℕ} (J : Disorder N μ.maxDegree)
    (x : Vector N) :
    field (fun p : Degree μ.maxDegree =>
      (centerMixture μ q hq).coeff p.val.val) J x =
      field (centerCoefficients (mixtureCoefficients μ) q) J x := by
  rw [centerMixture_coefficients μ q hq]

/-- The center sphere is precisely the radial image of the original
radius-`sqrt N` sphere. -/
theorem centerSphere_eq_radial_image (N : ℕ) (q : ℝ) (hq : 0 < q) :
    {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q} =
      (fun u : Vector N => Real.sqrt q • u) ''
        {u : Vector N | ‖u‖ ^ 2 = (N : ℝ)} := by
  have hs : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq.le
  have hsp : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hsn : Real.sqrt q ≠ 0 := hsp.ne'
  ext m
  constructor
  · intro hm
    refine ⟨(Real.sqrt q)⁻¹ • m, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_nonneg hsp.le, mul_pow]
      rw [inv_pow, hm, hs]
      field_simp [hq.ne']
    · simp [smul_smul, hsn]
  · rintro ⟨u, hu, rfl⟩
    simp only [Set.mem_ofPred_eq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hsp.le, mul_pow]
    rw [hu, hs]
    ring

/-- Pathwise equality of center-ground maxima and the scaled-mixture
ground maximum on the original physical sphere. -/
theorem centerSphere_sup_eq_scaledMixture (μ : FiniteMixture) (q : ℝ)
    (hq : 0 < q) {N : ℕ} (J : Disorder N μ.maxDegree) :
    sSup ((field (mixtureCoefficients μ) J) ''
      {m : Vector N | ‖m‖ ^ 2 = (N : ℝ) * q}) =
    sSup ((field (fun p : Degree μ.maxDegree =>
      (centerMixture μ q hq).coeff p.val.val) J) ''
      {u : Vector N | ‖u‖ ^ 2 = (N : ℝ)}) := by
  rw [centerSphere_eq_radial_image N q hq, Set.image_image]
  have hfun : (field (mixtureCoefficients μ) J) ∘
      (fun u : Vector N => Real.sqrt q • u) =
      field (fun p : Degree μ.maxDegree =>
        (centerMixture μ q hq).coeff p.val.val) J := by
    funext u
    change field (mixtureCoefficients μ) J (Real.sqrt q • u) = _
    rw [← field_center_scale (mixtureCoefficients μ)
      (mixtureCoefficients_nonnegative μ) hq.le J u]
    exact (centerMixture_field μ q hq J u).symm
  change sSup (((field (mixtureCoefficients μ) J) ∘
      (fun u : Vector N => Real.sqrt q • u)) ''
      {u : Vector N | ‖u‖ ^ 2 = (N : ℝ)}) = _
  rw [hfun]

end SlowEquilibration.SourceLiteratureGroundStateRadialCoefficients
