-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinComparison
public import SlowEquilibration.SphericalGaussianInterpolation
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The ordinary coordinate projection from a larger actual Euclidean
Gaussian disorder. -/
def projectGaussian {α κ : Type*} [Fintype α] (f : α → κ) (g : EuclideanSpace ℝ κ) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun i => g (f i))

theorem projectGaussian_measurable {α κ : Type*} [Fintype α] [Fintype κ] (f : α → κ) :
    Measurable (projectGaussian f) := by
  have hm : Measurable (fun g : EuclideanSpace ℝ κ => fun i => g (f i)) :=
    measurable_pi_iff.mpr (fun i => (PiLp.continuous_apply 2 (fun _ : κ => ℝ) (f i)).measurable)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.continuous.measurable.comp hm

/-- Projection to any injectively selected coordinate family preserves its
actual independent standard Gaussian law. -/
theorem projectGaussian_hasLaw {α κ : Type*} [Fintype α] [Fintype κ]
    (f : α → κ) (hf : Function.Injective f) :
    HasLaw (projectGaussian f) (SYK.standardGaussianMeasureOnEuclidean α)
      (SYK.standardGaussianMeasureOnEuclidean κ) := by
  have hmκ : Measurable (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.continuous.measurable
  have hmα : Measurable (WithLp.toLp 2 : (α → ℝ) → EuclideanSpace ℝ α) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : α => ℝ)).symm.continuous.measurable
  have hind : iIndepFun (fun i (z : κ → ℝ) => z (f i)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    (iIndepFun_pi (X := fun (_ : κ) (x : ℝ) => x)
      (fun _ => measurable_id.aemeasurable)).precomp hf
  have hlaw : HasLaw (fun z : κ → ℝ => fun i : α => z (f i))
      (Measure.pi (fun _ : α => gaussianReal 0 1)) (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    hind.hasLaw_pi (fun i => (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) (f i)).hasLaw)
  have hraw := (hasLaw_map hmα.aemeasurable).fun_comp hlaw
  refine ⟨(projectGaussian_measurable f).aemeasurable, ?_⟩
  rw [SYK.standardGaussianMeasureOnEuclidean, Measure.map_map (projectGaussian_measurable f) hmκ]
  exact hraw.map_eq

abbrev GuerraCoordinate (N P : ℕ) := Sum (Coordinate N P) (Fin N)
abbrev GuerraDisorder (N P : ℕ) := EuclideanSpace ℝ (GuerraCoordinate N P)

def guerraLabel {N P : ℕ} : GuerraCoordinate N P → Bool
  | Sum.inl _ => true
  | Sum.inr _ => false

/-- The mixed tensor and linear Gaussian trial fields, on disjoint actual
independent disorder coordinates. -/
def guerraFeature {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ) (x : Vector N) : GuerraDisorder N P :=
  WithLp.toLp 2 (fun i => match i with
    | Sum.inl j => β * fieldFeature c x j
    | Sum.inr j => Real.sqrt κ * x j)

def guerraLinear {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ) (x : Vector N) : GuerraDisorder N P →L[ℝ] ℝ :=
  innerSL ℝ (guerraFeature c β κ x)

theorem guerraFeature_continuous {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ) :
    Continuous (guerraFeature (N := N) c β κ) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : GuerraCoordinate N P => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j => exact continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Coordinate N P => ℝ) j).comp (fieldFeature_continuous c))
  | inr j => exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) j)

theorem guerraLinear_measurable {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ) :
    Measurable (guerraLinear (N := N) c β κ) :=
  ((innerSL ℝ).continuous.comp (guerraFeature_continuous c β κ)).measurable

theorem guerraFeature_norm_sq {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    ‖guerraFeature c β κ x‖^2 = (N : ℝ)*(β^2*covariancePolynomial c 1+κ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [guerraFeature, Fintype.sum_sum_type, mul_pow, Real.sq_sqrt hκ]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq,
    ← EuclideanSpace.real_norm_sq_eq, fieldFeature_norm_sq hN c hc x hx, hx]
  ring

theorem guerraLinear_bound {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∀ᵐ x ∂sphereLaw N, ‖guerraLinear c β κ x‖ ≤
      Real.sqrt ((N : ℝ)*(β^2*covariancePolynomial c 1+κ)) := by
  filter_upwards [sphereLaw_support hN] with x hx
  rw [guerraLinear, innerSL_apply_norm, ← guerraFeature_norm_sq hN c hc β hκ x hx,
    Real.sqrt_sq (norm_nonneg _)]

theorem guerra_coordinateObservable {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (x : Vector N) (i : GuerraCoordinate N P) :
    GaussianSpinComparison.coordinateObservable (guerraLinear c β κ) i x = guerraFeature c β κ x i := by
  rw [GaussianSpinComparison.coordinateObservable, guerraLinear, innerSL_apply_apply,
    EuclideanSpace.inner_single_right]
  simp only [conj_trivial, one_mul]

/-- The comparison's signed kernel is the genuine linear-trial covariance
minus the physical mixed-tensor covariance. -/
theorem guerra_signedKernel {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) (x y : Vector N) :
    GaussianSpinComparison.signedKernel (guerraLinear c β κ) guerraLabel x y =
      (N : ℝ)*(κ*overlap x y - β^2*covariancePolynomial c (overlap x y)) := by
  unfold GaussianSpinComparison.signedKernel
  simp only [guerra_coordinateObservable, Fintype.sum_sum_type, GaussianSpinComparison.covarianceSign,
    guerraLabel, guerraFeature, Bool.false_eq_true, ite_true, ite_false]
  have hm : (∑ i : Coordinate N P, -1*((β*fieldFeature c x i)*(β*fieldFeature c y i))) =
      -β^2 * inner ℝ (fieldFeature c x) (fieldFeature c y) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hl : (∑ i : Fin N, 1*((Real.sqrt κ*x i)*(Real.sqrt κ*y i))) = κ*inner ℝ x y := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = (Real.sqrt κ)^2*(y i*x i) := by ring
      _ = _ := by rw [Real.sq_sqrt hκ]
  rw [hm, hl, fieldFeature_inner_gram hN c hc]
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp only [overlap]
  field_simp
  ring

theorem overlap_mem_Icc_of_norm_sq {N : ℕ} (hN : 1 ≤ N) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) : overlap x y ∈ Icc (-1) 1 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hxn : ‖x‖ = Real.sqrt (N : ℝ) := by rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  have hyn : ‖y‖ = Real.sqrt (N : ℝ) := by rw [← hy, Real.sqrt_sq (norm_nonneg _)]
  have hi : |inner ℝ x y| ≤ (N : ℝ) := by
    simpa only [hxn, hyn, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg N)] using abs_real_inner_le_norm x y
  have hbound : |overlap x y| ≤ 1 := by
    rw [overlap, abs_div, abs_of_pos hNr]
    exact (div_le_iff₀ hNr).mpr (by simpa only [one_mul] using hi)
  exact abs_le.mp hbound

theorem sphereLaw_prod_support {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ z : Vector N × Vector N ∂(sphereLaw N).prod (sphereLaw N),
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_eq (continuous_fst.norm.pow 2) continuous_const).measurableSet.inter
      (isClosed_eq (continuous_snd.norm.pow 2) continuous_const).measurableSet)).mpr
  filter_upwards [sphereLaw_support hN] with x hx
  filter_upwards [sphereLaw_support hN] with y hy
  exact ⟨hx, hy⟩

theorem convex_covariance_supporting_line (μ : FiniteMixture)
    (hc : ConvexOn ℝ (Icc (-1) 1) μ.xi) {q : ℝ} (hq : q ∈ Icc (-1) 1)
    {r : ℝ} (hr : r ∈ Icc (-1) 1) : μ.xi q + μ.xi1 q * (r-q) ≤ μ.xi r := by
  rcases lt_trichotomy q r with hlt | heq | hgt
  · have h := hc.le_slope_of_hasDerivAt hq hr hlt (μ.hasDerivAt_xi q)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    linarith
  · subst r
    simp only [sub_self, mul_zero, add_zero, le_refl]
  · have h := hc.slope_le_of_hasDerivAt hr hq hgt (μ.hasDerivAt_xi q)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    nlinarith

theorem mixture_first_derivative_nonneg (μ : FiniteMixture) {q : ℝ} (hq : 0 ≤ q) : 0 ≤ μ.xi1 q := by
  unfold FiniteMixture.xi1
  exact Finset.sum_nonneg fun p _ => mul_nonneg
    (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)) (pow_nonneg hq _)

/-- The actual finite-volume Gaussian Guerra comparison with a linear
spherical trial field. The convex-covariance condition is explicit; extending
this condition to general odd mixtures requires the positivity argument. -/
theorem spherical_guerra_rotation_bound {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (hc : ConvexOn ℝ (Icc (-1) 1) μ.xi) {q : ℝ} (hq : q ∈ Icc 0 1) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw N)
      (guerraLinear (mixtureCoefficients μ) β (β^2*μ.xi1 q)) guerraLabel 0 ≤
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw N)
      (guerraLinear (mixtureCoefficients μ) β (β^2*μ.xi1 q)) guerraLabel (Real.pi/2) +
      ((N : ℝ)*β^2/2) * (μ.xi 1-μ.xi q-(1-q)*μ.xi1 q) := by
  let κ := β^2*μ.xi1 q
  have hκ : 0 ≤ κ := mul_nonneg (sq_nonneg _) (mixture_first_derivative_nonneg μ hq.1)
  have hdiag : ∀ᵐ x ∂sphereLaw N,
      GaussianSpinComparison.signedKernel (guerraLinear (mixtureCoefficients μ) β κ) guerraLabel x x =
        (N : ℝ)*(κ-β^2*μ.xi 1) := by
    filter_upwards [sphereLaw_support hN] with x hx
    rw [guerra_signedKernel hN _ (mixtureCoefficients_nonnegative μ) β hκ,
      overlap_self (lt_of_lt_of_le Nat.zero_lt_one hN) x hx, covariancePolynomial_mixture, mul_one]
  have hpair : ∀ᵐ z : Vector N × Vector N ∂(sphereLaw N).prod (sphereLaw N),
      GaussianSpinComparison.signedKernel (guerraLinear (mixtureCoefficients μ) β κ) guerraLabel z.1 z.2 ≤
        (N : ℝ)*β^2*(q*μ.xi1 q-μ.xi q) := by
    filter_upwards [sphereLaw_prod_support hN] with z hz
    rw [guerra_signedKernel hN _ (mixtureCoefficients_nonnegative μ) β hκ, covariancePolynomial_mixture]
    have ht := convex_covariance_supporting_line μ hc ⟨by linarith [hq.1], hq.2⟩
      (overlap_mem_Icc_of_norm_sq hN z.1 z.2 hz.1 hz.2)
    have hs := mul_le_mul_of_nonneg_left ht (sq_nonneg β)
    have hb : κ*overlap z.1 z.2-β^2*μ.xi (overlap z.1 z.2) ≤ β^2*(q*μ.xi1 q-μ.xi q) := by
      dsimp [κ]
      nlinarith
    exact (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg N)).trans_eq (by ring)
  have h := GaussianSpinComparison.gaussian_covariance_comparison (sphereLaw N)
    (guerraLinear (mixtureCoefficients μ) β κ) (guerraLinear_measurable _ β κ) (Real.sqrt_nonneg _)
    (guerraLinear_bound hN _ (mixtureCoefficients_nonnegative μ) β hκ) guerraLabel hdiag hpair
  convert h using 1
  dsimp [κ]
  ring

theorem guerraLinear_rotation_zero {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (x : Vector N) (g : GuerraDisorder N P) :
    guerraLinear c β κ x (GaussianSpinComparison.rotation guerraLabel 0 g) =
      β * field c (unpackDisorder (projectGaussian Sum.inl g)) x := by
  rw [guerraLinear, innerSL_apply_apply, ← fieldFeature_inner]
  simp [PiLp.inner_apply, RCLike.inner_apply, guerraFeature, Fintype.sum_sum_type,
    GaussianSpinComparison.rotation_apply, GaussianSpinComparison.rotationCoefficient, guerraLabel,
    projectGaussian, Finset.mul_sum, mul_assoc, mul_comm]

theorem guerraLinear_rotation_pi_div_two {N P : ℕ} (c : Degree P → ℝ) (β κ : ℝ)
    (x : Vector N) (g : GuerraDisorder N P) :
    guerraLinear c β κ x (GaussianSpinComparison.rotation guerraLabel (Real.pi/2) g) =
      Real.sqrt κ * inner ℝ (projectGaussian Sum.inr g) x := by
  rw [guerraLinear, innerSL_apply_apply]
  simp [PiLp.inner_apply, RCLike.inner_apply, guerraFeature, Fintype.sum_sum_type,
    GaussianSpinComparison.rotation_apply, GaussianSpinComparison.rotationCoefficient, guerraLabel,
    projectGaussian, Finset.mul_sum, mul_assoc, mul_comm]

/-- The actual linear Gaussian spherical trial pressure. Its variance
parameter is κ; the Gaussian vector has the literal standard product law. -/
def linearSphereQuenchedPressure (N : ℕ) (κ : ℝ) : ℝ :=
  (∫ g : Vector N, Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ g x))
    ∂SYK.standardGaussianMeasureOnEuclidean (Fin N)) / (N : ℝ)

theorem linearSphereLogPartition_integrable {N : ℕ} (hN : 1 ≤ N) {κ : ℝ} (_hκ : 0 ≤ κ) :
    Integrable (fun g : Vector N => Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ g x)))
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) := by
  let L : Vector N → Vector N →L[ℝ] ℝ := fun x => Real.sqrt κ • innerSL ℝ x
  have hLm : Measurable L :=
    ((innerSL ℝ).continuous.const_smul (Real.sqrt κ)).measurable
  have hbound : ∀ᵐ x ∂sphereLaw N, ‖L x‖ ≤ Real.sqrt κ * Real.sqrt (N : ℝ) := by
    filter_upwards [sphereLaw_support hN] with x hx
    have hxnorm : ‖x‖ = Real.sqrt (N : ℝ) := by rw [← hx, Real.sqrt_sq (norm_nonneg _)]
    simp only [L, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg κ), innerSL_apply_norm, hxnorm, le_refl]
  have h := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw N) L hLm
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hbound 1
  convert h using 1
  funext g
  congr 1
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight, L, one_smul, one_mul, innerSL_apply_apply,
      smul_apply, smul_eq_mul, real_inner_comm]

theorem guerraMean_zero_eq_physical {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (β κ : ℝ) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw N) (guerraLinear c β κ) guerraLabel 0 =
      ∫ J : Disorder N P, Real.log (partition N β (field c J)) ∂disorderLaw N P := by
  let f := fun g : EuclideanDisorder N P => Real.log (partition N β (field c (unpackDisorder g)))
  have hi : Integrable f (SYK.standardGaussianMeasureOnEuclidean (Coordinate N P)) := by
    have h := GaussianSpinInterpolation.logPartition_radial_gaussian_integrable (sphereLaw N) (sphereLinear c)
      (sphereLinear_measurable c) (Real.sqrt_nonneg _) (sphereLinear_bound hN c hc) β
    convert h using 1
    funext g
    simp only [f, GaussianSpinInterpolation.logPartition, gaussianMoment_eq_partition]
  have hm := (projectGaussian_hasLaw (Sum.inl : Coordinate N P → GuerraCoordinate N P) Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  calc
    _ = ∫ g : GuerraDisorder N P, f (projectGaussian Sum.inl g)
        ∂SYK.standardGaussianMeasureOnEuclidean (GuerraCoordinate N P) := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        change Real.log (GaussianSpinInterpolation.moment (sphereLaw N) (fun _ => 1)
          (guerraLinear c β κ) (GaussianSpinComparison.rotation guerraLabel 0 g)) =
          Real.log (partition N β (field c (unpackDisorder (projectGaussian Sum.inl g))))
        congr 1
        apply integral_congr_ae
        exact .of_forall fun x => by simp only [GaussianSpinInterpolation.weight, one_mul, guerraLinear_rotation_zero]
    _ = ∫ g : EuclideanDisorder N P, f g ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N P) := hm
    _ = _ := by
      rw [← gaussianMeanLogPartition_eq hN c hc]
      apply integral_congr_ae
      exact .of_forall fun g => by
        simp only [f, GaussianSpinInterpolation.logPartition, gaussianMoment_eq_partition]

theorem guerraMean_pi_div_two_eq_linear {N P : ℕ} (hN : 1 ≤ N) (c : Degree P → ℝ)
    (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ) :
    GaussianSpinComparison.averagedRotatedLogPartition (sphereLaw N) (guerraLinear c β κ) guerraLabel (Real.pi/2) =
      ∫ g : Vector N, Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ g x))
        ∂SYK.standardGaussianMeasureOnEuclidean (Fin N) := by
  have h := (projectGaussian_hasLaw (Sum.inr : Fin N → GuerraCoordinate N P) Sum.inr_injective).integral_comp
    (linearSphereLogPartition_integrable hN hκ).aestronglyMeasurable
  calc
    _ = ∫ g : GuerraDisorder N P, Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ (projectGaussian Sum.inr g) x))
        ∂SYK.standardGaussianMeasureOnEuclidean (GuerraCoordinate N P) := by
      apply integral_congr_ae
      exact .of_forall fun g => by
        change Real.log (GaussianSpinInterpolation.moment (sphereLaw N) (fun _ => 1)
          (guerraLinear c β κ) (GaussianSpinComparison.rotation guerraLabel (Real.pi/2) g)) =
          Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ (projectGaussian Sum.inr g) x))
        congr 1
        apply integral_congr_ae
        exact .of_forall fun x => by
          simp only [GaussianSpinInterpolation.weight, one_mul, guerraLinear_rotation_pi_div_two]
    _ = _ := h

/-- The replica-symmetric spherical Guerra upper comparison on the literal
finite mixed Gaussian model, with the actual Gaussian linear trial pressure.
This is a finite-volume comparison, not the unproved thermodynamic formula. -/
theorem quenchedPressure_le_linearTrial {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ)
    (hc : ConvexOn ℝ (Icc (-1) 1) μ.xi) {q : ℝ} (hq : q ∈ Icc 0 1) :
    quenchedPressure N μ β ≤ linearSphereQuenchedPressure N (β^2*μ.xi1 q) +
      (β^2/2)*(μ.xi 1-μ.xi q-(1-q)*μ.xi1 q) := by
  have h := spherical_guerra_rotation_bound hN μ β hc hq
  rw [guerraMean_zero_eq_physical hN _ (mixtureCoefficients_nonnegative μ),
    guerraMean_pi_div_two_eq_linear hN _ β
      (mul_nonneg (sq_nonneg _) (mixture_first_derivative_nonneg μ hq.1))] at h
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  unfold quenchedPressure linearSphereQuenchedPressure
  apply (div_le_iff₀ hNr).mpr
  convert h using 1
  · rfl
  · field_simp

end
end SlowEquilibration.SphericalModel
