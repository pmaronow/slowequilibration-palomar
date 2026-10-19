-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PositiveDensityL2Unitary
public import SlowEquilibration.SphericalGroundStateConjugation

/-! The literal normalized Gibbs L² unitary and C² generator conjugation. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalForm
open MeasureTheory Filter Set SphericalModel
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def groundStateWeight (N : ℕ) (β : ℝ) (H : Vector N → ℝ) (x : Vector N) : ℝ :=
  Real.exp (β / 2 * H x) / Real.sqrt (partition N β H)

theorem groundStateWeight_pos {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (x : Vector N) :
    0 < groundStateWeight N β H x :=
  div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (partition_pos hN β hH))

theorem groundStateWeight_continuous {N : ℕ} (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) : Continuous (groundStateWeight N β H) :=
  (Real.continuous_exp.comp (continuous_const.mul hH)).div_const _

theorem groundStateWeight_contDiff {N : ℕ} (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 2 H) : ContDiff ℝ 2 (groundStateWeight N β H) :=
  ((contDiff_const.mul hH).exp).div_const _

theorem groundStateWeight_sq {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (x : Vector N) :
    groundStateWeight N β H x ^ 2 = gibbsDensity N β H x := by
  unfold groundStateWeight gibbsDensity
  rw [div_pow, Real.sq_sqrt (partition_pos hN β hH).le, sq, ← Real.exp_add]
  congr 2
  ring

theorem gibbsLaw_eq_groundStateDensity {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) :
    gibbsLaw N β H = (sphereLaw N).withDensity
      (fun x => ENNReal.ofReal (groundStateWeight N β H x ^ 2)) := by
  simp only [groundStateWeight_sq hN β hH, gibbsLaw]

/-- Actual unitary from normalized Gibbs L² to the original uniform sphere L². -/
def groundStateUnitary {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) :
    Lp ℝ 2 (gibbsLaw N β H) ≃ₗᵢ[ℝ] Lp ℝ 2 (sphereLaw N) :=
  PositiveDensityL2.unitary (sphereLaw N) (gibbsLaw N β H) (groundStateWeight N β H)
    (groundStateWeight_continuous β hH).measurable (groundStateWeight_pos hN β hH)
    (gibbsLaw_eq_groundStateDensity hN β hH)

theorem groundStateUnitary_coe {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (gibbsLaw N β H)) :
    groundStateUnitary hN β H hH f =ᵐ[sphereLaw N]
      (fun x => groundStateWeight N β H x * f x) :=
  PositiveDensityL2.unitary_coe _ _ _ _ _ _ f

theorem groundStateUnitary_symm_coe {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Lp ℝ 2 (sphereLaw N)) :
    (groundStateUnitary hN β H hH).symm f =ᵐ[gibbsLaw N β H]
      (fun x => f x / groundStateWeight N β H x) :=
  PositiveDensityL2.unitary_symm_coe _ _ _ _ _ _ f

theorem rotationGenerator_const_mul_onSphere {N : ℕ} (hN : N ≠ 0) (β c : ℝ)
    (H : Vector N → ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    rotationGenerator N β H (fun y => c * f y) x = c * rotationGenerator N β H f x := by
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  rw [rotationGenerator_sum_onSphere hN β H _ x hx,
    rotationGenerator_sum_onSphere hN β H _ x hx]
  have hD (A : Operator N) : lieDerivative A (fun y => c * f y) =
      fun y => c * lieDerivative A f y := funext (lieDerivative_const_mul A c hf1)
  simp_rw [hD, lieDerivative_const_mul _ c (lieDerivative_contDiff_one _ hf)]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem groundState_normalized_conjugation {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    groundStateWeight N β H x *
      (-rotationGenerator N β H (fun y => f y / groundStateWeight N β H y) x) =
        -rotationLaplacian N f x + groundStatePotential N β H x * f x := by
  have hfun : (fun y => f y / groundStateWeight N β H y) =
      fun y => Real.sqrt (partition N β H) * (Real.exp (-(β / 2) * H y) * f y) := by
    funext y
    unfold groundStateWeight
    simp only [neg_mul, Real.exp_neg]
    field_simp
  rw [hfun, rotationGenerator_const_mul_onSphere (by omega) β _ H
    (((contDiff_const.mul hH).exp).mul hf) x hx,
    rotationGenerator_groundState (by omega) β hH hf x hx]
  unfold groundStateWeight
  have hZ := (Real.sqrt_pos.mpr (partition_pos hN β hH.continuous)).ne'
  simp only [neg_mul, Real.exp_neg]
  field_simp [hZ]
  ring

theorem memLp_sphere_of_continuous {N : ℕ} (hN : 1 ≤ N)
    {f : Vector N → ℝ} (hf : Continuous f) : MemLp f 2 (sphereLaw N) :=
  (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (integrable_sphere_of_continuous hN (hf.pow 2))

def groundSphereToL2 {N : ℕ} (hN : 1 ≤ N) (f : Vector N → ℝ) (hf : Continuous f) :
    Lp ℝ 2 (sphereLaw N) := (memLp_sphere_of_continuous hN hf).toLp f

theorem groundSphereToL2_coe {N : ℕ} (hN : 1 ≤ N) (f : Vector N → ℝ) (hf : Continuous f) :
    groundSphereToL2 hN f hf =ᵐ[sphereLaw N] f := MemLp.coeFn_toLp _

theorem groundStateUnitary_symm_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) (hf : Continuous f) :
    (groundStateUnitary hN β H hH).symm (groundSphereToL2 hN f hf) =
      gibbsToL2 hN β H hH (fun x => f x / groundStateWeight N β H x)
        (hf.div (groundStateWeight_continuous β hH)
          (fun x => (groundStateWeight_pos hN β hH x).ne')) := by
  apply Lp.ext
  filter_upwards [groundStateUnitary_symm_coe hN β H hH _,
    (groundSphereToL2_coe hN f hf).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le,
    gibbsToL2_coe hN β H hH _ _] with x hx hy hz
  rw [hx, hy, hz]

/-- True self-adjoint form generator, unitarily conjugated on every C² test. -/
theorem sphericalGenerator_groundState_C2 {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (f : Vector N → ℝ)
    (hf : ContDiff ℝ 2 f) :
    ∃ hdom : (groundStateUnitary hN β H hH.continuous).symm
        (groundSphereToL2 hN f hf.continuous) ∈
          (sphericalGenerator hN β H hH.continuous).domain,
      groundStateUnitary hN β H hH.continuous
        (sphericalGenerator hN β H hH.continuous
          ⟨(groundStateUnitary hN β H hH.continuous).symm
            (groundSphereToL2 hN f hf.continuous),hdom⟩) =
      groundSphereToL2 hN
        (fun x => -rotationLaplacian N f x + groundStatePotential N β H x * f x)
        ((rotationLaplacian_continuous hf).neg.add
          ((groundStatePotential_continuous β hH).mul hf.continuous)) := by
  have hq : ContDiff ℝ 2 (fun x => f x / groundStateWeight N β H x) :=
    hf.div (groundStateWeight_contDiff β hH)
      (fun x => (groundStateWeight_pos hN β hH.continuous x).ne')
  rw [groundStateUnitary_symm_continuous hN β H hH.continuous f hf.continuous]
  obtain ⟨hd,hA⟩ := sphericalGenerator_C2 hN β H (hH.of_le (by norm_num)) _ hq
  refine ⟨hd,?_⟩
  rw [hA]
  apply Lp.ext
  have hac := PositiveDensityL2.reverse_absolutelyContinuous (sphereLaw N)
    (gibbsLaw N β H) (groundStateWeight N β H)
    (groundStateWeight_continuous β hH.continuous).measurable
    (groundStateWeight_pos hN β hH.continuous)
    (gibbsLaw_eq_groundStateDensity hN β hH.continuous)
  let k := rotationGenerator N β H (fun x => f x / groundStateWeight N β H x)
  have hk : Continuous k := rotationGenerator_continuous β (hH.of_le (by norm_num)) hq
  let v := gibbsToL2 hN β H hH.continuous k hk
  filter_upwards [groundStateUnitary_coe hN β H hH.continuous (-v),
    (Lp.coeFn_neg v).filter_mono hac.ae_le,
    (gibbsToL2_coe hN β H hH.continuous k hk).filter_mono hac.ae_le,
    groundSphereToL2_coe hN
      (fun x => -rotationLaplacian N f x + groundStatePotential N β H x * f x)
      ((rotationLaplacian_continuous hf).neg.add
        ((groundStatePotential_continuous β hH).mul hf.continuous)),
    sphereLaw_support hN] with x hx hn hg hs hxs
  change (groundStateUnitary hN β H hH.continuous (-v)) x = _
  change v x = k x at hg
  simp only [hx, hn, Pi.neg_apply, hg, hs]
  exact groundState_normalized_conjugation hN β hH hf x ((onSphere_iff_norm_sq x).mpr hxs)

theorem groundStatePotential_memLp_mul {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (f : Lp ℝ 2 (sphereLaw N)) :
    MemLp (fun x => groundStatePotential N β H x * f x) 2 (sphereLaw N) := by
  obtain ⟨C,hC⟩ := groundStatePotential_bounded β hH
  apply (Lp.memLp f).of_le_mul
    ((groundStatePotential_continuous β hH).aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (c := C)
  filter_upwards [sphereLaw_support hN] with x hx
  rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (hC x ((onSphere_iff_norm_sq x).mpr hx)) (norm_nonneg _)

/-- The potential term is a genuine bounded multiplication operator. -/
def groundStatePotentialLinear {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    Lp ℝ 2 (sphereLaw N) →ₗ[ℝ] Lp ℝ 2 (sphereLaw N) where
  toFun f := (groundStatePotential_memLp_mul hN β hH f).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH (f+g)),
      MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH f),
      MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH g),
      Lp.coeFn_add f g, Lp.coeFn_add
        ((groundStatePotential_memLp_mul hN β hH f).toLp _)
        ((groundStatePotential_memLp_mul hN β hH g).toLp _)] with x hfg hf hg ha ha'
    simp only [hfg,ha,ha',Pi.add_apply,hf,hg,mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH (c • f)),
      MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH f), Lp.coeFn_smul c f,
      Lp.coeFn_smul c ((groundStatePotential_memLp_mul hN β hH f).toLp _)]
      with x hcf hf hs hs'
    simp only [RingHom.id_apply,hcf,hs,hs',Pi.smul_apply,smul_eq_mul,hf]
    ring

theorem groundStatePotentialLinear_coe {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) (f : Lp ℝ 2 (sphereLaw N)) :
    groundStatePotentialLinear hN β H hH f =ᵐ[sphereLaw N]
      (fun x => groundStatePotential N β H x * f x) :=
  MemLp.coeFn_toLp (groundStatePotential_memLp_mul hN β hH f)

theorem groundStatePotentialLinear_bound {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    ∃ C : ℝ, ∀ f, ‖groundStatePotentialLinear hN β H hH f‖ ≤ C * ‖f‖ := by
  obtain ⟨C,hC⟩ := groundStatePotential_bounded β hH
  refine ⟨C,fun f => Lp.norm_le_mul_norm_of_ae_le_mul ?_⟩
  filter_upwards [groundStatePotentialLinear_coe hN β H hH f,sphereLaw_support hN]
    with x hx hs
  rw [hx,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right
    (hC x ((onSphere_iff_norm_sq x).mpr hs)) (norm_nonneg _)

def groundStatePotentialOperator {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    Lp ℝ 2 (sphereLaw N) →L[ℝ] Lp ℝ 2 (sphereLaw N) :=
  (groundStatePotentialLinear hN β H hH).mkContinuous
    (groundStatePotentialLinear_bound hN β H hH).choose
    (groundStatePotentialLinear_bound hN β H hH).choose_spec

theorem groundStatePotentialOperator_selfAdjoint {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : ContDiff ℝ 2 H) :
    IsSelfAdjoint (groundStatePotentialOperator hN β H hH) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro f g
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [groundStatePotentialLinear_coe hN β H hH f,
    groundStatePotentialLinear_coe hN β H hH g] with x hf hg
  change inner ℝ (groundStatePotentialLinear hN β H hH f x) (g x) =
    inner ℝ (f x) (groundStatePotentialLinear hN β H hH g x)
  simp only [hf,hg,RCLike.inner_apply,conj_trivial]
  ring

end SlowEquilibration.SphericalForm
