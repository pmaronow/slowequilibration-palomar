-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceEntranceHarmonicFinal
public import SlowEquilibration.SourceEntranceGoodEvent
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import SlowEquilibration.OrderedTensorSingleProjectedTrace
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Probability.Independence.InfinitePi

/-! All spherical harmonic sectors of the original ordered Gaussian tensors
in manuscript Section 8, `lem:ent-harmonic`(4). Trace-adjoint lifts of the
explicit Gegenbauer kernels produce actual coefficient projections. A
self-adjoint angular operator proves their orthogonality; their homogeneous
extensions have zero Euclidean Laplacian. Exact reconstruction, joint Gaussian
laws, simultaneous independence across mixture degrees, and the literal
Gamma-weight zonal covariances are proved.

The nested `FullEvent` namespace constructs the complete entrance event,
including every harmonic-sector source-scale bound, and transfers all entrance
estimates to conditioning on this same event. The latitude MGF theorem retains
the previously documented sphere logarithmic Sobolev hypothesis.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceHarmonicSectors

open MeasureTheory ProbabilityTheory SphericalModel SourceEntranceHarmonic
open SourceEntranceHarmonicFinal
open SphericalAging.FiniteModel hiding Vector
open SphericalAging.OrthogonalGaussianDisclosure
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false

-- RADIAL_HELPERS_BEGIN

open Laplacian

private theorem radial_nat_mul_pow_pred (a : ℝ) (n : ℕ) :
    (n : ℝ) * a^(n-1) * a = (n : ℝ) * a^n := by
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel, pow_succ]; ring

private theorem radial_nat_mul_pred_pow (a : ℝ) (n : ℕ) :
    (n : ℝ) * (n-1 : ℕ) * a^(n-2) * a =
      (n : ℝ) * (n-1 : ℕ) * a^(n-1) := by
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero => simp
    | succ n =>
      rw [show n+1+1-1 = n+1 by omega, show n+1+1-2 = n by omega, pow_succ]
      ring

private theorem radial_nat_mul_pred_cast (n : ℕ) :
    (n : ℝ) * (n-1 : ℕ) = (n : ℝ) * ((n : ℝ)-1) := by
  cases n with
  | zero => simp
  | succ n => simp

private theorem radialMonomial_second (N q s : ℕ) (x y v : Vector N) :
    iteratedFDeriv ℝ 2 (fun z : Vector N => (‖z‖^2)^s * (inner ℝ x z)^q)
      y (fun _ => v) =
      (2*(s : ℝ)*(‖y‖^2)^(s-1)*(inner ℝ x y)^q) * ‖v‖^2 +
      (4*(s : ℝ)*(s-1 : ℕ)*(‖y‖^2)^(s-2)*(inner ℝ x y)^q) * (inner ℝ y v)^2 +
      (4*(s : ℝ)*(q : ℝ)*(‖y‖^2)^(s-1)*(inner ℝ x y)^(q-1)) *
        (inner ℝ y v * inner ℝ x v) +
      ((q : ℝ)*(q-1 : ℕ)*(‖y‖^2)^s*(inner ℝ x y)^(q-2)) * (inner ℝ x v)^2 := by
  let R : Vector N → ℝ := fun z => ‖z‖^2
  let T : Vector N →L[ℝ] ℝ := innerSL ℝ x
  have hR (z : Vector N) : HasFDerivAt R ((2 : ℝ) • innerSL ℝ z) z := by
    simpa only [R, two_smul] using (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hT (z : Vector N) : HasFDerivAt T T z := T.hasFDerivAt
  have hd (z : Vector N) : HasFDerivAt (fun w => (R w)^s * (T w)^q)
      ((2*(s : ℝ)*(R z)^(s-1)*(T z)^q) • innerSL ℝ z +
        ((q : ℝ)*(R z)^s*(T z)^(q-1)) • T) z := by
    convert ((hR z).pow s).mul ((hT z).pow q) using 1
    ext u
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have he : fderiv ℝ (fun z => (R z)^s * (T z)^q) = fun z =>
      (2*(s : ℝ)*(R z)^(s-1)*(T z)^q) • innerSL ℝ z +
        ((q : ℝ)*(R z)^s*(T z)^(q-1)) • T :=
    funext (fun z => (hd z).fderiv)
  have hA := (((hR y).pow (s-1)).const_mul (2*(s : ℝ))).mul ((hT y).pow q)
  have hB := (((hR y).pow s).const_mul (q : ℝ)).mul ((hT y).pow (q-1))
  have hD := (hA.smul
    ((innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ).hasFDerivAt (x := y))).add
      (hB.smul_const T)
  change HasFDerivAt (fun z =>
    (2*(s : ℝ)*(R z)^(s-1)*(T z)^q) • innerSL ℝ z +
      ((q : ℝ)*(R z)^s*(T z)^(q-1)) • T) _ y at hD
  change iteratedFDeriv ℝ 2 (fun z => (R z)^s * (T z)^q) y (fun _ => v) = _
  rw [iteratedFDeriv_two_apply, he, hD.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_eq_mul, Pi.mul_apply, Nat.sub_sub, Nat.reduceAdd]
  rw [show ((innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) v) v = inner ℝ v v by rfl,
    show ((innerSL ℝ : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) y) v = inner ℝ y v by rfl,
    show T y = inner ℝ x y by rfl, show T v = inner ℝ x v by rfl]
  dsimp only [R]
  rw [real_inner_self_eq_norm_sq]
  ring

/-- The genuine Euclidean Laplacian on every radial monomial, including
zero radial or axial degree. This supplies the local differential step in
the arbitrary harmonic-sector construction. -/
private theorem radialMonomial_laplacian (N q s : ℕ) (x y : Vector N) :
    Δ (fun z : Vector N => (‖z‖^2)^s * (inner ℝ x z)^q) y =
      2*(s : ℝ)*((N : ℝ)+2*s+2*q-2)*(‖y‖^2)^(s-1)*(inner ℝ x y)^q +
      (q : ℝ)*((q : ℝ)-1)*‖x‖^2*(‖y‖^2)^s*(inner ℝ x y)^(q-2) := by
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  have hcross : (∑ i : Fin N, inner ℝ y (e i) * inner ℝ x (e i)) = inner ℝ x y := by
    simp_rw [real_inner_comm (e _) x]
    rw [e.sum_inner_mul_inner, real_inner_comm]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ e]
  simp only
  have ht (i : Fin N) : (![e i, e i] : Fin 2 → Vector N) = (fun _ => e i) := by
    funext k
    fin_cases k <;> rfl
  simp_rw [ht, radialMonomial_second]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [e.sum_sq_inner_left, e.sum_sq_inner_left, hcross]
  have hn : (∑ i : Fin N, ‖e i‖^2) = (N : ℝ) := by simp
  rw [hn]
  have hs := radial_nat_mul_pred_pow (‖y‖^2) s
  have hq := radial_nat_mul_pow_pred (inner ℝ x y) q
  have hsc := radial_nat_mul_pred_cast s
  have hqc := radial_nat_mul_pred_cast q
  linear_combination 4*(inner ℝ x y)^q*hs +
    4*(s : ℝ)*(‖y‖^2)^(s-1)*hq +
    4*(‖y‖^2)^(s-1)*(inner ℝ x y)^q*hsc +
    ‖x‖^2*(‖y‖^2)^s*(inner ℝ x y)^(q-2)*hqc

/-- Multiplication by squared radius removes the radial predecessor
power. The angular operator therefore acts triangularly, in every degree,
with the literal spherical-harmonic eigenvalue on the diagonal. -/
private theorem radialMonomial_angular (N q s : ℕ) (x y : Vector N) :
    ‖y‖^2 * Δ (fun z : Vector N => (‖z‖^2)^s * (inner ℝ x z)^q) y -
      ((q+2*s : ℕ) : ℝ)*(((q+2*s : ℕ) : ℝ)+(N : ℝ)-2)*
        ((‖y‖^2)^s*(inner ℝ x y)^q) =
      -(q : ℝ)*((q : ℝ)+(N : ℝ)-2)*((‖y‖^2)^s*(inner ℝ x y)^q) +
      (q : ℝ)*((q : ℝ)-1)*‖x‖^2*(‖y‖^2)^(s+1)*(inner ℝ x y)^(q-2) := by
  rw [radialMonomial_laplacian, pow_succ]
  push_cast
  have hs := radial_nat_mul_pow_pred (‖y‖^2) s
  linear_combination 2*((N : ℝ)+2*s+2*q-2)*(inner ℝ x y)^q*hs

-- RADIAL_HELPERS_END

-- TRACE_HELPERS_BEGIN

def rawFeature (N p : ℕ) (x : Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  PureTensorJetFeatures.tensorFeature (fun _ : Fin p => x)

private theorem rawFeature_inner (N p : ℕ) (x y : Vector N) :
    inner ℝ (rawFeature N p x) (rawFeature N p y) = (inner ℝ x y)^p := by
  simp only [rawFeature, PureTensorJetFeatures.tensorFeature_inner,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

private theorem rawFeature_contDiff (N p : ℕ) : ContDiff ℝ ⊤ (rawFeature N p) := by
  apply (contDiff_piLp 2).2
  intro I
  change ContDiff ℝ ⊤ (fun x : Vector N => ∏ k : Fin p, x (I k))
  fun_prop

private theorem rawFeature_smul (N p : ℕ) (r : ℝ) (x : Vector N) :
    rawFeature N p (r • x) = r^p • rawFeature N p x := by
  ext I
  change (∏ k : Fin p, r * x (I k)) = r^p * ∏ k : Fin p, x (I k)
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

private theorem rawFeature_zero (N p : ℕ) (hp : 1 ≤ p) : rawFeature N p 0 = 0 := by
  have h := rawFeature_smul N p 0 (0 : Vector N)
  simpa only [zero_smul, zero_pow (by omega : p ≠ 0)] using h

def rawCoefficientSpace (N p : ℕ) : Submodule ℝ
    (EuclideanSpace ℝ (TensorIndex N p)) :=
  Submodule.span ℝ (Set.range (rawFeature N p))

private theorem rawFeature_mem (N p : ℕ) (x : Vector N) :
    rawFeature N p x ∈ rawCoefficientSpace N p :=
  Submodule.subset_span ⟨x, rfl⟩

private theorem rawFeature_projection (N p : ℕ) (x : Vector N) :
    (rawCoefficientSpace N p).starProjection (rawFeature N p x) = rawFeature N p x :=
  Submodule.starProjection_eq_self_iff.mpr (rawFeature_mem N p x)

private theorem rawCoefficient_separation {N p : ℕ}
    (v : EuclideanSpace ℝ (TensorIndex N p)) (hv : v ∈ rawCoefficientSpace N p)
    (h : ∀ y : Vector N, inner ℝ v (rawFeature N p y) = 0) : v = 0 := by
  have hz : ∀ w ∈ rawCoefficientSpace N p, inner ℝ v w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => obtain ⟨y, rfl⟩ := hw; exact h y
    | zero => simp
    | add w z _ _ hw hz => simp only [inner_add_right, hw, hz, add_zero]
    | smul r w _ hw => simp only [real_inner_smul_right, hw, mul_zero]
  exact inner_self_eq_zero.mp (hz v hv)

private theorem rawCoefficient_sphere_separation {N p : ℕ} (hN : 1 ≤ N)
    (hp : 1 ≤ p) (v : EuclideanSpace ℝ (TensorIndex N p))
    (hv : v ∈ rawCoefficientSpace N p)
    (h : ∀ y : Vector N, ‖y‖^2 = (N : ℝ) → inner ℝ v (rawFeature N p y) = 0) :
    v = 0 := by
  apply rawCoefficient_separation v hv
  intro y
  by_cases hy : y = 0
  · rw [hy, rawFeature_zero N p hp, inner_zero_right]
  · have hn := SphericalAging.SphereInitialLaw.normalize_norm_sq y hy
    have hh := h (SphericalAging.SphereInitialLaw.normalize N y) hn
    rw [SphericalAging.SphereInitialLaw.normalize, rawFeature_smul,
      real_inner_smul_right] at hh
    have hr : (Real.sqrt (N : ℝ) / ‖y‖)^p ≠ 0 :=
      pow_ne_zero _ (div_ne_zero
        (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < N by omega))).ne'
        (norm_ne_zero_iff.mpr hy))
    exact (mul_eq_zero.mp hh).resolve_left hr

def tensorCast {N p q : ℕ} (h : p = q) :
    EuclideanSpace ℝ (TensorIndex N p) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (TensorIndex N q) := by
  subst q
  exact LinearIsometryEquiv.refl ℝ _

private theorem tensorCast_raw {N p q : ℕ} (h : p = q) (x : Vector N) :
    tensorCast (N := N) h (rawFeature N p x) = rawFeature N q x := by
  subst q
  rfl

def rawTrace (N q s : ℕ) :
    EuclideanSpace ℝ (TensorIndex N (q+s+s)) →L[ℝ]
      EuclideanSpace ℝ (TensorIndex N q) :=
  GaussianFiniteFeatures.observation (fun a => innerSL ℝ
    (OrderedTensorTraceGaussianBank.rawTraceFeature N q s a))

private theorem rawTrace_apply (N q s : ℕ)
    (z : EuclideanSpace ℝ (TensorIndex N (q+s+s))) (a : TensorIndex N q) :
    rawTrace N q s z a = ∑ b : TensorIndex N s,
      z (OrderedTensorTraceGaussianBank.tracedIndex a b) := by
  rw [rawTrace, GaussianFiniteFeatures.observation_apply, innerSL_apply_apply,
    OrderedTensorTraceGaussianBank.rawTraceFeature, sum_inner]
  simp only [EuclideanSpace.basisFun_inner]

private theorem rawTrace_rawFeature (N q s : ℕ) (x : Vector N) :
    rawTrace N q s (rawFeature N (q+s+s) x) = ‖x‖^(2*s) • rawFeature N q x := by
  ext a
  rw [rawTrace_apply]
  change (∑ b : TensorIndex N s,
    tensorMonomial x (OrderedTensorTraceGaussianBank.tracedIndex a b)) =
      ‖x‖^(2*s) * tensorMonomial x a
  have hterm (b : TensorIndex N s) :
      tensorMonomial x (OrderedTensorTraceGaussianBank.tracedIndex a b) =
        tensorMonomial x a * (tensorMonomial x b * tensorMonomial x b) := by
    change tensorMonomial x (OrderedTensorTraceGaussianBank.fullTensorIndex a b b) = _
    rw [OrderedTensorTraceGaussianBank.tensorMonomial_fullTensorIndex]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hs : (∑ b : TensorIndex N s, tensorMonomial x b * tensorMonomial x b) =
      (inner ℝ x x)^s := by
    simpa only [rawFeature, PureTensorJetFeatures.tensorFeature,
      PiLp.inner_apply, RCLike.inner_apply, conj_trivial, tensorMonomial] using
      rawFeature_inner N s x x
  rw [hs, real_inner_self_eq_norm_sq, ← pow_mul]
  ring

def traceLift {N p q s : ℕ} (h : q+s+s = p) :
    EuclideanSpace ℝ (TensorIndex N q) →L[ℝ]
      EuclideanSpace ℝ (TensorIndex N p) :=
  (tensorCast (N := N) h).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (rawTrace N q s).adjoint

private theorem traceLift_kernel {N p q s : ℕ} (h : q+s+s = p) (x y : Vector N) :
    inner ℝ ((rawCoefficientSpace N p).starProjection
      (traceLift (N := N) h (rawFeature N q x))) (rawFeature N p y) =
        ‖y‖^(2*s) * (inner ℝ x y)^q := by
  calc
    _ = inner ℝ (traceLift (N := N) h (rawFeature N q x))
        ((rawCoefficientSpace N p).starProjection (rawFeature N p y)) :=
      (rawCoefficientSpace N p).starProjection_isSymmetric _ _
    _ = inner ℝ (traceLift (N := N) h (rawFeature N q x)) (rawFeature N p y) := by
      rw [rawFeature_projection]
    _ = _ := by
      subst p
      change inner ℝ ((rawTrace N q s).adjoint (rawFeature N q x))
        (rawFeature N (q+s+s) y) = _
      rw [(rawTrace N q s).adjoint_inner_left, rawTrace_rawFeature,
        real_inner_smul_right, rawFeature_inner]

def zonalKernelLift (N p : ℕ) (i : Fin (p/2+1)) (x : Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) :=
  ((N : ℝ)^(p-i.val))⁻¹ •
    ∑ k : Fin ((p-2*i.val)/2+1),
      (zonalCoefficient N (p-2*i.val) k.val * ‖x‖^(2*k.val)) •
        (rawCoefficientSpace N p).starProjection
          (traceLift (N := N) (q := p-2*i.val-2*k.val) (s := i.val+k.val)
            (by have hi := i.isLt; have hk := k.isLt; omega)
            (rawFeature N (p-2*i.val-2*k.val) x))

private theorem zonalKernelLift_mem (N p : ℕ) (i : Fin (p/2+1)) (x : Vector N) :
    zonalKernelLift N p i x ∈ rawCoefficientSpace N p := by
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k _
  exact Submodule.smul_mem _ _ ((rawCoefficientSpace N p).starProjection_apply_mem _)

private theorem zonalKernelLift_pairing (N p : ℕ) (i : Fin (p/2+1))
    (x y : Vector N) :
    inner ℝ (zonalKernelLift N p i x) (rawFeature N p y) =
      ((N : ℝ)^(p-i.val))⁻¹ *
        ∑ k : Fin ((p-2*i.val)/2+1),
          zonalCoefficient N (p-2*i.val) k.val * ‖x‖^(2*k.val) *
            ‖y‖^(2*(i.val+k.val)) * (inner ℝ x y)^(p-2*i.val-2*k.val) := by
  simp only [zonalKernelLift, real_inner_smul_left, sum_inner, traceLift_kernel,
    mul_assoc]

open InnerProductSpace Laplacian

private theorem innerPower_second (N p : ℕ) (z y v : Vector N) :
    iteratedFDeriv ℝ 2 (fun w : Vector N => (inner ℝ z w)^p) y (fun _ => v) =
      (p.descFactorial 2 : ℝ) * (inner ℝ z y)^(p-2) * (inner ℝ z v)^2 := by
  change iteratedFDeriv ℝ 2 ((fun t : ℝ => t^p) ∘ innerSL ℝ z) y (fun _ => v) = _
  rw [(innerSL ℝ z).iteratedFDeriv_comp_right
    (show ContDiff ℝ ⊤ (fun t : ℝ => t^p) by fun_prop) y (by simp)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    innerSL_apply_apply, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    iteratedDeriv_pow, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

private theorem innerPower_laplacian (N p : ℕ) (z y : Vector N) :
    Δ (fun w : Vector N => (inner ℝ z w)^p) y =
      (p.descFactorial 2 : ℝ) * ‖z‖^2 * (inner ℝ z y)^(p-2) := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin N) ℝ)]
  have hdir (i : Fin N) :
      (![EuclideanSpace.basisFun (Fin N) ℝ i,
        EuclideanSpace.basisFun (Fin N) ℝ i] : Fin 2 → Vector N) =
        (fun _ => EuclideanSpace.basisFun (Fin N) ℝ i) := by
    funext k
    fin_cases k <;> rfl
  simp_rw [hdir, innerPower_second]
  rw [← Finset.mul_sum, (EuclideanSpace.basisFun (Fin N) ℝ).sum_sq_inner_left]
  ring

private def traceOne (N p : ℕ) :
    EuclideanSpace ℝ (TensorIndex N p) →L[ℝ]
      EuclideanSpace ℝ (TensorIndex N (p-2)) :=
  if hp : 2 ≤ p then
    (rawTrace N (p-2) 1).comp
      (tensorCast (N := N) (by omega : p = p-2+1+1)).toContinuousLinearEquiv.toContinuousLinearMap
  else 0

private theorem traceOne_rawFeature (N p : ℕ) (x : Vector N) :
    (p.descFactorial 2 : ℝ) • traceOne N p (rawFeature N p x) =
      ((p.descFactorial 2 : ℝ)*‖x‖^2) • rawFeature N (p-2) x := by
  unfold traceOne
  split_ifs with hp
  · rw [ContinuousLinearMap.comp_apply]
    change (p.descFactorial 2 : ℝ) • rawTrace N (p-2) 1
      (tensorCast (N := N) (by omega : p = p-2+1+1) (rawFeature N p x)) = _
    rw [tensorCast_raw, rawTrace_rawFeature]
    simp only [Nat.mul_one, smul_smul]
  · have hp' : p = 0 ∨ p = 1 := by omega
    rcases hp' with rfl | rfl <;> simp

private theorem rawCoefficient_laplacian {N p : ℕ}
    (v : EuclideanSpace ℝ (TensorIndex N p)) (hv : v ∈ rawCoefficientSpace N p)
    (y : Vector N) :
    Δ (fun w : Vector N => inner ℝ v (rawFeature N p w)) y =
      (p.descFactorial 2 : ℝ) * inner ℝ (traceOne N p v) (rawFeature N (p-2) y) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨z, rfl⟩ := hv
      have he : (fun w : Vector N => inner ℝ (rawFeature N p z) (rawFeature N p w)) =
          (fun w => (inner ℝ z w)^p) := funext (rawFeature_inner N p z)
      rw [he, innerPower_laplacian]
      have ht := congrArg (fun u => inner ℝ u (rawFeature N (p-2) y))
        (traceOne_rawFeature N p z)
      simp only [real_inner_smul_left, rawFeature_inner] at ht
      rw [ht]
  | zero => simp
  | add v w _ _ hv hw =>
      have hcV : ContDiff ℝ 2 (fun z => inner ℝ v (rawFeature N p z)) :=
        (contDiff_const.inner ℝ (rawFeature_contDiff N p)).of_le (by simp)
      have hcW : ContDiff ℝ 2 (fun z => inner ℝ w (rawFeature N p z)) :=
        (contDiff_const.inner ℝ (rawFeature_contDiff N p)).of_le (by simp)
      have he : (fun z => inner ℝ (v+w) (rawFeature N p z)) =
          (fun z => inner ℝ v (rawFeature N p z)) +
            (fun z => inner ℝ w (rawFeature N p z)) := by
        funext z
        exact inner_add_left _ _ _
      rw [he, hcV.contDiffAt.laplacian_add hcW.contDiffAt, hv, hw]
      simp only [map_add, inner_add_left, mul_add]
  | smul r v _ hv =>
      have hc : ContDiff ℝ 2 (fun z => inner ℝ v (rawFeature N p z)) :=
        (contDiff_const.inner ℝ (rawFeature_contDiff N p)).of_le (by simp)
      have he : (fun z => inner ℝ (r • v) (rawFeature N p z)) =
          r • (fun z => inner ℝ v (rawFeature N p z)) := by
        funext z
        exact real_inner_smul_left _ _ _
      rw [he, laplacian_smul r hc.contDiffAt, hv]
      simp only [map_smul, real_inner_smul_left, smul_eq_mul]
      ring

private def angularEigenvalue (N p : ℕ) : ℝ := (p : ℝ)*(p+(N : ℝ)-2)

private def angularTrace (N p : ℕ) :
    EuclideanSpace ℝ (TensorIndex N p) →L[ℝ]
      EuclideanSpace ℝ (TensorIndex N (p-2)) :=
  (traceOne N p).comp (rawCoefficientSpace N p).starProjection

private def angularOperator (N p : ℕ) :
    EuclideanSpace ℝ (TensorIndex N p) →L[ℝ]
      EuclideanSpace ℝ (TensorIndex N p) :=
  (p.descFactorial 2 : ℝ) • ((angularTrace N p).adjoint.comp (angularTrace N p)) -
    angularEigenvalue N p • (rawCoefficientSpace N p).starProjection

private theorem angularOperator_symmetric (N p : ℕ) :
    (angularOperator N p).toLinearMap.IsSymmetric := by
  intro v w
  change inner ℝ (angularOperator N p v) w = inner ℝ v (angularOperator N p w)
  simp only [angularOperator, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [(angularTrace N p).adjoint_inner_left, (angularTrace N p).adjoint_inner_right]
  have hP : inner ℝ ((rawCoefficientSpace N p).starProjection v) w =
      inner ℝ v ((rawCoefficientSpace N p).starProjection w) :=
    (rawCoefficientSpace N p).starProjection_isSymmetric v w
  rw [hP]

private theorem angularOperator_mem (N p : ℕ)
    (v : EuclideanSpace ℝ (TensorIndex N p)) :
    angularOperator N p v ∈ rawCoefficientSpace N p := by
  have hP : (rawCoefficientSpace N p).starProjection.adjoint =
      (rawCoefficientSpace N p).starProjection :=
    (rawCoefficientSpace N p).starProjection_isSymmetric.clm_adjoint_eq
  change (p.descFactorial 2 : ℝ) •
    ((angularTrace N p).adjoint (angularTrace N p v)) -
      angularEigenvalue N p • (rawCoefficientSpace N p).starProjection v ∈ _
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    rw [angularTrace, ContinuousLinearMap.adjoint_comp, hP,
      ContinuousLinearMap.comp_apply]
    exact (rawCoefficientSpace N p).starProjection_apply_mem _
  · exact Submodule.smul_mem _ _ ((rawCoefficientSpace N p).starProjection_apply_mem v)

private theorem angularOperator_pairing {N p : ℕ}
    (v : EuclideanSpace ℝ (TensorIndex N p)) (hv : v ∈ rawCoefficientSpace N p)
    (y : Vector N) :
    inner ℝ (angularOperator N p v) (rawFeature N p y) =
      ‖y‖^2 * Δ (fun w : Vector N => inner ℝ v (rawFeature N p w)) y -
        angularEigenvalue N p * inner ℝ v (rawFeature N p y) := by
  have hPv : (rawCoefficientSpace N p).starProjection v = v :=
    Submodule.starProjection_eq_self_iff.mpr hv
  simp only [angularOperator, sub_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    inner_sub_left, real_inner_smul_left]
  rw [(angularTrace N p).adjoint_inner_left]
  simp only [angularTrace, ContinuousLinearMap.comp_apply, hPv, rawFeature_projection]
  rw [rawCoefficient_laplacian v hv y]
  have ht := congrArg (fun z => inner ℝ (traceOne N p v) z)
    (traceOne_rawFeature N p y)
  simp only [real_inner_smul_right] at ht
  rw [ht]
  ring

private theorem zonalKernelLift_sphere {N : ℕ} (hN : 3 ≤ N) (p : ℕ)
    (i : Fin (p/2+1)) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) :
    inner ℝ (zonalKernelLift N p i x) (rawFeature N p y) =
      zonal N (p-2*i.val) (overlap x y) := by
  rw [zonalKernelLift_pairing, zonal_eq_sum, ← Fin.sum_univ_eq_sum_range,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hi : 2*i.val ≤ p := by have := i.isLt; omega
  have hk : 2*k.val ≤ p-2*i.val := by have := k.isLt; omega
  have hd : p-i.val = (p-2*i.val-2*k.val) + (k.val+(i.val+k.val)) := by omega
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hs : ((N : ℝ)^(p-i.val))⁻¹ * (N : ℝ)^k.val * (N : ℝ)^(i.val+k.val) =
      ((N : ℝ)^(p-2*i.val-2*k.val))⁻¹ := by
    rw [hd]
    simp only [pow_add]
    field_simp
  have hxx : ‖x‖^(2*k.val) = (N : ℝ)^k.val := by rw [pow_mul, hx]
  have hyy : ‖y‖^(2*(i.val+k.val)) = (N : ℝ)^(i.val+k.val) := by rw [pow_mul, hy]
  rw [hxx, hyy]
  unfold overlap
  rw [div_pow]
  calc
    _ = (((N : ℝ)^(p-i.val))⁻¹ * (N : ℝ)^k.val * (N : ℝ)^(i.val+k.val)) *
        (zonalCoefficient N (p-2*i.val) k.val *
          (inner ℝ x y)^(p-2*i.val-2*k.val)) := by ring
    _ = _ := by rw [hs]; ring

private theorem zonalKernelLift_contDiff (N p : ℕ) (i : Fin (p/2+1)) :
    ContDiff ℝ ⊤ (zonalKernelLift N p i) := by
  unfold zonalKernelLift
  apply ContDiff.const_smul
  apply ContDiff.sum
  intro k _
  have hn : ContDiff ℝ ⊤ (fun x : Vector N => ‖x‖^(2*k.val)) := by
    simpa only [pow_mul] using
      (contDiff_norm_sq ℝ : ContDiff ℝ ⊤ (fun x : Vector N => ‖x‖^2)).pow k.val
  exact (contDiff_const.mul hn).smul
    ((rawCoefficientSpace N p).starProjection.contDiff.comp
      ((traceLift (N := N) (q := p-2*i.val-2*k.val) (s := i.val+k.val)
        (by have hi := i.isLt; have hk := k.isLt; omega)).contDiff.comp
        (rawFeature_contDiff N (p-2*i.val-2*k.val))))

private theorem zonalKernelLift_homogeneous (N p : ℕ) (i : Fin (p/2+1))
    (r : ℝ) (x : Vector N) :
    zonalKernelLift N p i (r • x) = r^(p-2*i.val) • zonalKernelLift N p i x := by
  unfold zonalKernelLift
  rw [smul_comm (r^(p-2*i.val))]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : 2*k.val ≤ p-2*i.val := by have := k.isLt; omega
  have he : 2*k.val+(p-2*i.val-2*k.val) = p-2*i.val := by omega
  simp only [rawFeature_smul, map_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, (even_two_mul k.val).pow_abs, smul_smul]
  congr 1
  have hr : r^(2*k.val)*r^(p-2*i.val-2*k.val) = r^(p-2*i.val) := by
    rw [← pow_add, he]
  linear_combination (zonalCoefficient N (p-2*i.val) k.val * ‖x‖^(2*k.val))*hr

-- TRACE_HELPERS_END

-- SPECTRAL_HELPERS_BEGIN

section SpectralProjectionAlgebra

variable {E S I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

omit [FiniteDimensional ℝ E] in
private theorem eigenfeature_inner_zero (A : E →L[ℝ] E)
    (hA : ∀ v w, inner ℝ (A v) w = inner ℝ v (A w))
    {a b : ℝ} (hab : a ≠ b) {v w : E}
    (hv : A v = a • v) (hw : A w = b • w) :
    inner ℝ v w = 0 := by
  have he := hA v w
  rw [hv, hw, real_inner_smul_left, real_inner_smul_right] at he
  have hz : (a-b)*inner ℝ v w = 0 := by nlinarith
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)

omit [FiniteDimensional ℝ E] [Fintype I] in
private theorem featureSpans_orthogonal (h : I → S → E)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℝ (h i x) (h j y) = 0) :
    Pairwise (fun i j => Submodule.span ℝ (Set.range (h i)) ⟂
      Submodule.span ℝ (Set.range (h j))) := by
  intro i j hij
  apply Submodule.isOrtho_span.mpr
  rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩
  exact horth i j hij x y

private theorem projection_of_orthogonal_feature_sum
    (f : S → E) (h : I → S → E) (a : I → ℝ)
    (hreconstruct : ∀ x, f x = ∑ i, a i • h i x)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℝ (h i x) (h j y) = 0)
    (i : I) (x : S) :
    (Submodule.span ℝ (Set.range (h i))).starProjection (f x) = a i • h i x := by
  classical
  let W := fun j => Submodule.span ℝ (Set.range (h j))
  have hW : Pairwise (fun i j => W i ⟂ W j) := featureSpans_orthogonal h horth
  change (W i).starProjection (f x) = _
  rw [hreconstruct x, map_sum]
  simp only [map_smul]
  rw [Finset.sum_eq_single i]
  · rw [Submodule.starProjection_eq_self_iff.mpr
      (Submodule.subset_span (Set.mem_range_self x))]
  · intro j _ hji
    have hz : (W i).starProjection (h j x) = 0 := by
      apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((W i).zero_mem)
      intro w hw
      rw [sub_zero]
      exact (hW hji).inner_eq (Submodule.subset_span (Set.mem_range_self x)) hw
    rw [hz, smul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem gram_of_orthogonal_feature_sum
    (f : S → E) (h : I → S → E) (a : I → ℝ) (K : I → S → S → ℝ)
    (hreconstruct : ∀ x, f x = ∑ i, a i • h i x)
    (horth : ∀ i j, i ≠ j → ∀ x y, inner ℝ (h i x) (h j y) = 0)
    (hkernel : ∀ i x y, inner ℝ (h i x) (f y) = K i x y)
    (i : I) (x y : S) :
    inner ℝ (a i • h i x) (a i • h i y) = a i * K i x y := by
  let W := Submodule.span ℝ (Set.range (h i))
  have hp := projection_of_orthogonal_feature_sum f h a hreconstruct horth i y
  have hm : a i • h i x ∈ W :=
    W.smul_mem _ (Submodule.subset_span (Set.mem_range_self x))
  calc
    _ = inner ℝ (a i • h i x) (W.starProjection (f y)) := by rw [hp]
    _ = inner ℝ (W.starProjection (a i • h i x)) (f y) :=
      (W.inner_starProjection_left_eq_right _ _).symm
    _ = inner ℝ (a i • h i x) (f y) := by
      rw [Submodule.starProjection_eq_self_iff.mpr hm]
    _ = _ := by rw [real_inner_smul_left, hkernel]

end SpectralProjectionAlgebra

private theorem homogeneousZonal_cancellation {N : ℕ} (hN : 3 ≤ N)
    (ell j : ℕ) (a b r : ℝ) :
    (∑ k ∈ Finset.range (ell/2+1), zonalCoefficient N ell k *
      ((((ell : ℝ)*(ell+(N : ℝ)-2)) -
          ((ell-2*k : ℕ) : ℝ)*((ell-2*k : ℕ)+(N : ℝ)-2)) *
            a^k*b^(j+k)*r^(ell-2*k) +
        ((ell-2*k).descFactorial 2 : ℝ)*
          a^(k+1)*b^(j+k+1)*r^(ell-2*k-2))) = 0 := by
  let A : ℕ → ℝ := fun k => zonalCoefficient N ell k *
    ((ell-2*k).descFactorial 2 : ℝ) * a^(k+1)*b^(j+k+1)*r^(ell-2*k-2)
  let B : ℕ → ℝ := fun k => zonalCoefficient N ell k *
    (((ell : ℝ)*(ell+(N : ℝ)-2)) -
      ((ell-2*k : ℕ) : ℝ)*((ell-2*k : ℕ)+(N : ℝ)-2)) *
        a^k*b^(j+k)*r^(ell-2*k)
  have hB0 : B 0 = 0 := by simp [B]
  have hAlast : A (ell/2) = 0 := by
    have hq : ell-2*(ell/2) = 0 ∨ ell-2*(ell/2) = 1 := by omega
    rcases hq with hq | hq <;> simp [A, hq, Nat.descFactorial_succ]
  have hstep (k : ℕ) (hk : k < ell/2) : B (k+1) = -A k := by
    have hq : 2*(k+1) ≤ ell := by omega
    have hkell : k+1 ≤ ell := by omega
    have he :
        ((ell : ℝ)*(ell+(N : ℝ)-2)) -
          ((ell-2*(k+1) : ℕ) : ℝ)*((ell-2*(k+1) : ℕ)+(N : ℝ)-2) =
            4*(k+1 : ℕ)*(alpha N+(ell-(k+1) : ℕ)) := by
      simp only [Nat.cast_sub hq, Nat.cast_sub hkell, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
      unfold alpha
      ring
    have hc := zonalCoefficient_adjacent hN hq
    have hd : ((ell-2*k).descFactorial 2 : ℝ) =
        (ell-2*k : ℕ)*(ell-2*k-1 : ℕ) := by
      simp [Nat.descFactorial_succ, mul_comm]
    dsimp only [A, B]
    rw [he, hc, hd,
      show ell-2*(k+1) = ell-2*k-2 by omega,
      show j+(k+1) = j+k+1 by omega]
    ring
  have heq : (∑ k ∈ Finset.range (ell/2+1), zonalCoefficient N ell k *
      ((((ell : ℝ)*(ell+(N : ℝ)-2)) -
          ((ell-2*k : ℕ) : ℝ)*((ell-2*k : ℕ)+(N : ℝ)-2)) *
            a^k*b^(j+k)*r^(ell-2*k) +
        ((ell-2*k).descFactorial 2 : ℝ)*
          a^(k+1)*b^(j+k+1)*r^(ell-2*k-2))) =
        (∑ k ∈ Finset.range (ell/2+1), A k) +
          ∑ k ∈ Finset.range (ell/2+1), B k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [A, B]
    ring
  rw [heq, Finset.sum_range_succ, Finset.sum_range_succ', hAlast, hB0]
  simp only [add_zero]
  have hs : (∑ k ∈ Finset.range (ell/2), B (k+1)) =
      -(∑ k ∈ Finset.range (ell/2), A k) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact hstep k (Finset.mem_range.mp hk)
  rw [hs, add_neg_cancel]



private def homogeneousZonalKernel (N ell j : ℕ) (x y : Vector N) : ℝ :=
  ∑ k ∈ Finset.range (ell/2+1), zonalCoefficient N ell k *
    (‖x‖^2)^k*(‖y‖^2)^(j+k)*(inner ℝ x y)^(ell-2*k)

private theorem homogeneousZonalKernel_angular {N : ℕ} (hN : 3 ≤ N)
    (ell j : ℕ) (x y : Vector N) :
    ‖y‖^2 * Δ (homogeneousZonalKernel N ell j x) y -
      ((ell+2*j : ℕ) : ℝ)*(((ell+2*j : ℕ) : ℝ)+(N : ℝ)-2)*
        homogeneousZonalKernel N ell j x y =
      -(ell : ℝ)*((ell : ℝ)+(N : ℝ)-2)*homogeneousZonalKernel N ell j x y := by
  let e := EuclideanSpace.basisFun (Fin N) ℝ
  let F : ℕ → Vector N → ℝ := fun k z =>
    (‖z‖^2)^(j+k)*(inner ℝ x z)^(ell-2*k)
  have hF (k : ℕ) : ContDiff ℝ ⊤ (F k) := by
    dsimp [F]
    exact ((contDiff_norm_sq ℝ : ContDiff ℝ ⊤ (fun z : Vector N => ‖z‖^2)).pow _).mul
      ((contDiff_const.inner ℝ contDiff_id).pow _)
  have hLap :
      Δ (homogeneousZonalKernel N ell j x) y =
        ∑ k ∈ Finset.range (ell/2+1),
          (zonalCoefficient N ell k*(‖x‖^2)^k)*Δ (F k) y := by
    have hsum : homogeneousZonalKernel N ell j x =
        fun z => ∑ k ∈ Finset.range (ell/2+1),
          (zonalCoefficient N ell k*(‖x‖^2)^k) • F k z := by
      funext z
      unfold homogeneousZonalKernel
      apply Finset.sum_congr rfl
      intro k _
      dsimp [F]
      ring
    rw [hsum]
    rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
      (fun z => ∑ k ∈ Finset.range (ell/2+1),
        (zonalCoefficient N ell k*(‖x‖^2)^k) • F k z) e) y]
    change (∑ a : Fin N, iteratedFDeriv ℝ 2
      (fun z => ∑ k ∈ Finset.range (ell/2+1),
        (zonalCoefficient N ell k*(‖x‖^2)^k) • F k z) y ![e a,e a]) = _
    simp_rw [iteratedFDeriv_fun_sum_apply
      (f := fun k z => (zonalCoefficient N ell k*(‖x‖^2)^k) • F k z)
      (n := 2) (x := y) (fun k _ =>
      ((hF k).const_smul _).contDiffAt.of_le (by simp))]
    simp only [sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    simp_rw [iteratedFDeriv_const_smul_apply' ((hF k).contDiffAt.of_le (by simp)),
      smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    exact (congrFun
      (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (F k) e) y).symm
  have hsum :
      ‖y‖^2 * Δ (homogeneousZonalKernel N ell j x) y -
        ((ell+2*j : ℕ) : ℝ)*(((ell+2*j : ℕ) : ℝ)+(N : ℝ)-2)*
          homogeneousZonalKernel N ell j x y +
        (ell : ℝ)*((ell : ℝ)+(N : ℝ)-2)*homogeneousZonalKernel N ell j x y =
      ∑ k ∈ Finset.range (ell/2+1), zonalCoefficient N ell k *
        ((((ell : ℝ)*(ell+(N : ℝ)-2)) -
            ((ell-2*k : ℕ) : ℝ)*((ell-2*k : ℕ)+(N : ℝ)-2)) *
              (‖x‖^2)^k*(‖y‖^2)^(j+k)*(inner ℝ x y)^(ell-2*k) +
          ((ell-2*k).descFactorial 2 : ℝ)*
            (‖x‖^2)^(k+1)*(‖y‖^2)^(j+k+1)*(inner ℝ x y)^(ell-2*k-2)) := by
    rw [hLap]
    unfold homogeneousZonalKernel
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : 2*k ≤ ell := by have := Finset.mem_range.mp hk; omega
    have ht := radialMonomial_angular N (ell-2*k) (j+k) x y
    have hp : ell-2*k+2*(j+k) = ell+2*j := by omega
    rw [hp] at ht
    have hd : ((ell-2*k).descFactorial 2 : ℝ) =
        ((ell-2*k : ℕ) : ℝ)*(((ell-2*k : ℕ) : ℝ)-1) := by
      cases hq : ell-2*k with
      | zero => simp [Nat.descFactorial_succ]
      | succ q => simp [Nat.descFactorial_succ]; ring
    rw [hd, pow_succ (‖x‖^2) k]
    change _ = _
    dsimp [F]
    linear_combination (zonalCoefficient N ell k*(‖x‖^2)^k)*ht
  rw [homogeneousZonal_cancellation hN ell j (‖x‖^2) (‖y‖^2) (inner ℝ x y)] at hsum
  linarith


private theorem homogeneousZonalKernel_contDiff (N ell j : ℕ) (x : Vector N) :
    ContDiff ℝ ⊤ (homogeneousZonalKernel N ell j x) := by
  unfold homogeneousZonalKernel
  apply ContDiff.sum
  intro k _
  exact (contDiff_const.mul ((contDiff_norm_sq ℝ).pow (j+k))).mul
    ((contDiff_const.inner ℝ contDiff_id).pow (ell-2*k))

private theorem zonalKernelLift_pairing_homogeneous (N p : ℕ)
    (i : Fin (p/2+1)) (x : Vector N) :
    (fun y => inner ℝ (zonalKernelLift N p i x) (rawFeature N p y)) =
      ((N : ℝ)^(p-i.val))⁻¹ • homogeneousZonalKernel N (p-2*i.val) i.val x := by
  funext y
  rw [zonalKernelLift_pairing]
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold homogeneousZonalKernel
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp only [pow_mul]

private theorem zonalKernelLift_eigen {N : ℕ} (hN : 3 ≤ N)
    (p : ℕ) (i : Fin (p/2+1)) (x : Vector N) :
    angularOperator N p (zonalKernelLift N p i x) =
      (-angularEigenvalue N (p-2*i.val)) • zonalKernelLift N p i x := by
  apply sub_eq_zero.mp
  apply rawCoefficient_separation
    (angularOperator N p (zonalKernelLift N p i x) -
      (-angularEigenvalue N (p-2*i.val)) • zonalKernelLift N p i x)
    ((rawCoefficientSpace N p).sub_mem
      (angularOperator_mem N p _) ((rawCoefficientSpace N p).smul_mem _
        (zonalKernelLift_mem N p i x)))
  intro y
  rw [inner_sub_left, angularOperator_pairing _ (zonalKernelLift_mem N p i x),
    real_inner_smul_left, zonalKernelLift_pairing_homogeneous]
  rw [congrFun (zonalKernelLift_pairing_homogeneous N p i x) y]
  rw [InnerProductSpace.laplacian_smul _
    ((homogeneousZonalKernel_contDiff N (p-2*i.val) i.val x).contDiffAt.of_le (by simp))]
  simp only [Pi.smul_apply, smul_eq_mul]
  have ht := homogeneousZonalKernel_angular hN (p-2*i.val) i.val x y
  have hi : p-2*i.val+2*i.val = p := by have := i.isLt; omega
  rw [hi] at ht
  unfold angularEigenvalue
  linear_combination ((N : ℝ)^(p-i.val))⁻¹ * ht

-- SPECTRAL_HELPERS_END

-- HARMONIC_HELPERS_BEGIN

private theorem homogeneousZonalKernel_symm (N ell : ℕ) (x y : Vector N) :
    homogeneousZonalKernel N ell 0 x y = homogeneousZonalKernel N ell 0 y x := by
  unfold homogeneousZonalKernel
  apply Finset.sum_congr rfl
  intro k _
  simp only [Nat.zero_add]
  rw [real_inner_comm x y]
  ring

private theorem homogeneousZonalKernel_factor (N ell j : ℕ) (x y : Vector N) :
    homogeneousZonalKernel N ell j x y =
      (‖y‖^2)^j * homogeneousZonalKernel N ell 0 x y := by
  unfold homogeneousZonalKernel
  simp only [Nat.zero_add, pow_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem homogeneousZonalKernel_laplacian {N : ℕ} (hN : 3 ≤ N)
    (ell : ℕ) (x y : Vector N) :
    Δ (homogeneousZonalKernel N ell 0 x) y = 0 := by
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  have hC : Continuous (Δ (homogeneousZonalKernel N ell 0 x)) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _
      (EuclideanSpace.basisFun (Fin N) ℝ)]
    apply continuous_finsetSum
    intro k _
    exact (continuous_eval_const
      (![EuclideanSpace.basisFun (Fin N) ℝ k,
        EuclideanSpace.basisFun (Fin N) ℝ k] : Fin 2 → Vector N)).comp
      ((homogeneousZonalKernel_contDiff N ell 0 x).continuous_iteratedFDeriv
        (m := 2) (by simp))
  have he : Δ (homogeneousZonalKernel N ell 0 x) = (fun _ => 0) := by
    apply Continuous.ext_on (dense_compl_singleton (0 : Vector N)) hC continuous_const
    intro z hz
    have hz0 : z ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hz
    have ht := homogeneousZonalKernel_angular hN ell 0 x z
    simp only [Nat.mul_zero, Nat.add_zero] at ht
    have hzero : ‖z‖^2 * Δ (homogeneousZonalKernel N ell 0 x) z = 0 := by linarith
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hz0))
  exact congrFun he y

private theorem zonalKernelLift_raw_laplacian {N : ℕ} (hN : 3 ≤ N)
    (p : ℕ) (i : Fin (p/2+1)) (z x : Vector N) :
    Δ (fun w : Vector N => inner ℝ (zonalKernelLift N p i w) (rawFeature N p z)) x = 0 := by
  have he : (fun w : Vector N => inner ℝ (zonalKernelLift N p i w) (rawFeature N p z)) =
      (((N : ℝ)^(p-i.val))⁻¹ * (‖z‖^2)^i.val) •
        homogeneousZonalKernel N (p-2*i.val) 0 z := by
    funext w
    have hk := congrFun (zonalKernelLift_pairing_homogeneous N p i w) z
    simp only [Pi.smul_apply, smul_eq_mul] at hk ⊢
    rw [hk, homogeneousZonalKernel_factor, homogeneousZonalKernel_symm]
    ring
  rw [he, InnerProductSpace.laplacian_smul _
    ((homogeneousZonalKernel_contDiff N (p-2*i.val) 0 z).contDiffAt.of_le (by simp)),
    homogeneousZonalKernel_laplacian hN]
  simp

private theorem zonalKernelLift_mem_laplacian {N : ℕ} (hN : 3 ≤ N)
    (p : ℕ) (i : Fin (p/2+1)) (z : EuclideanSpace ℝ (TensorIndex N p))
    (hz : z ∈ rawCoefficientSpace N p) (x : Vector N) :
    Δ (fun w : Vector N => inner ℝ (zonalKernelLift N p i w) z) x = 0 := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨y, rfl⟩ := hz
      exact zonalKernelLift_raw_laplacian hN p i y x
  | zero => simp
  | add z w _ _ hz hw =>
      have hcZ : ContDiff ℝ 2 (fun u => inner ℝ (zonalKernelLift N p i u) z) :=
        ((zonalKernelLift_contDiff N p i).inner ℝ contDiff_const).of_le (by simp)
      have hcW : ContDiff ℝ 2 (fun u => inner ℝ (zonalKernelLift N p i u) w) :=
        ((zonalKernelLift_contDiff N p i).inner ℝ contDiff_const).of_le (by simp)
      have he : (fun u => inner ℝ (zonalKernelLift N p i u) (z+w)) =
          (fun u => inner ℝ (zonalKernelLift N p i u) z) +
            (fun u => inner ℝ (zonalKernelLift N p i u) w) := by
        funext u
        exact inner_add_right _ _ _
      rw [he, hcZ.contDiffAt.laplacian_add hcW.contDiffAt, hz, hw]
      simp only [add_zero]
  | smul r z _ hz =>
      have hc : ContDiff ℝ 2 (fun u => inner ℝ (zonalKernelLift N p i u) z) :=
        ((zonalKernelLift_contDiff N p i).inner ℝ contDiff_const).of_le (by simp)
      have he : (fun u => inner ℝ (zonalKernelLift N p i u) (r • z)) =
          r • (fun u => inner ℝ (zonalKernelLift N p i u) z) := by
        funext u
        exact real_inner_smul_right _ _ _
      rw [he, InnerProductSpace.laplacian_smul _ hc.contDiffAt, hz, smul_zero]

private theorem zonalKernelLift_harmonic_evaluation {N : ℕ} (hN : 3 ≤ N)
    (p : ℕ) (i : Fin (p/2+1)) (z : EuclideanSpace ℝ (TensorIndex N p))
    (x : Vector N) :
    Δ (fun w : Vector N => inner ℝ (zonalKernelLift N p i w) z) x = 0 := by
  have he : (fun w => inner ℝ (zonalKernelLift N p i w) z) =
      (fun w => inner ℝ (zonalKernelLift N p i w)
        ((rawCoefficientSpace N p).starProjection z)) := by
    funext w
    have hP : (rawCoefficientSpace N p).starProjection (zonalKernelLift N p i w) =
        zonalKernelLift N p i w :=
      Submodule.starProjection_eq_self_iff.mpr (zonalKernelLift_mem N p i w)
    calc
      _ = inner ℝ ((rawCoefficientSpace N p).starProjection (zonalKernelLift N p i w)) z :=
        by rw [hP]
      _ = _ := (rawCoefficientSpace N p).starProjection_isSymmetric _ _
  rw [he]
  exact zonalKernelLift_mem_laplacian hN p i _
    ((rawCoefficientSpace N p).starProjection_apply_mem z) x

-- HARMONIC_HELPERS_END

-- ROTATION_HELPERS_BEGIN

private theorem rawFeature_rotated {N p : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) :
    SphericalAging.TensorOrthogonalAction.action (p := p) U (rawFeature N p x) =
      rawFeature N p (U x) := by
  exact SphericalAging.TensorOrthogonalAction.action_pureTensor U (fun _ : Fin p => x)

private theorem rawCoefficientSpace_rotated_mem {N p : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (v : EuclideanSpace ℝ (TensorIndex N p)) (hv : v ∈ rawCoefficientSpace N p) :
    SphericalAging.TensorOrthogonalAction.action U v ∈ rawCoefficientSpace N p := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨x, rfl⟩ := hv
      rw [rawFeature_rotated]
      exact rawFeature_mem N p (U x)
  | zero => simpa only [map_zero] using (rawCoefficientSpace N p).zero_mem
  | add v w _ _ hv hw =>
      rw [map_add]
      exact (rawCoefficientSpace N p).add_mem hv hw
  | smul r v _ hv =>
      rw [map_smul]
      exact (rawCoefficientSpace N p).smul_mem r hv

/-- The actual lifted zonal feature commutes with the genuine ordered
tensor action, in every ambient dimension and degree. -/
private theorem zonalKernelLift_rotated {N p : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (i : Fin (p/2+1)) (x : Vector N) :
    SphericalAging.TensorOrthogonalAction.action U (zonalKernelLift N p i x) =
      zonalKernelLift N p i (U x) := by
  apply sub_eq_zero.mp
  apply rawCoefficient_separation _
    ((rawCoefficientSpace N p).sub_mem
      (rawCoefficientSpace_rotated_mem U _ (zonalKernelLift_mem N p i x))
      (zonalKernelLift_mem N p i (U x)))
  intro y
  have hA := (SphericalAging.TensorOrthogonalAction.action (p := p) U).inner_map_map
    (zonalKernelLift N p i x) (rawFeature N p (U.symm y))
  rw [rawFeature_rotated, U.apply_symm_apply] at hA
  have hi : inner ℝ x (U.symm y) = inner ℝ (U x) y := by
    simpa only [U.apply_symm_apply] using (U.inner_map_map x (U.symm y)).symm
  rw [inner_sub_left, hA, zonalKernelLift_pairing, zonalKernelLift_pairing, hi]
  simp only [U.norm_map, U.symm.norm_map, sub_self]

-- ROTATION_HELPERS_END

-- PUBLIC_SECTORS_BEGIN

private theorem angularEigenvalue_injective {N : ℕ} (hN : 3 ≤ N) :
    Function.Injective (angularEigenvalue N) := by
  intro a b hab
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 0 < (a : ℝ)+(b : ℝ)+(N : ℝ)-2 := by
    nlinarith [(show (0 : ℝ) ≤ a from Nat.cast_nonneg a),
      (show (0 : ℝ) ≤ b from Nat.cast_nonneg b)]
  have hz : ((a : ℝ)-(b : ℝ))*((a : ℝ)+(b : ℝ)+(N : ℝ)-2) = 0 := by
    unfold angularEigenvalue at hab
    nlinarith [hab]
  have he : (a : ℝ) = (b : ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hs.ne')
  exact_mod_cast he

private theorem zonalKernelLift_orthogonal {N : ℕ} (hN : 3 ≤ N)
    (p : ℕ) (i j : Fin (p/2+1)) (hij : i ≠ j) (x y : Vector N) :
    inner ℝ (zonalKernelLift N p i x) (zonalKernelLift N p j y) = 0 := by
  have hd : p-2*i.val ≠ p-2*j.val := by
    intro he
    apply hij
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega
  have heigen : -angularEigenvalue N (p-2*i.val) ≠
      -angularEigenvalue N (p-2*j.val) := by
    intro he
    exact hd (angularEigenvalue_injective hN (neg_injective he))
  exact eigenfeature_inner_zero (angularOperator N p)
    (angularOperator_symmetric N p) heigen
    (zonalKernelLift_eigen hN p i x) (zonalKernelLift_eigen hN p j y)

private theorem zonalKernelLift_reconstruction {N p : ℕ} (hN : 3 ≤ N)
    (hp : 1 ≤ p) (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    rawFeature N p x =
      ∑ i : Fin (p/2+1), ((N : ℝ)^p*gammaWeight N p i.val) • zonalKernelLift N p i x := by
  apply sub_eq_zero.mp
  apply rawCoefficient_sphere_separation (by omega : 1 ≤ N) hp
    (rawFeature N p x -
      ∑ i : Fin (p/2+1), ((N : ℝ)^p*gammaWeight N p i.val) • zonalKernelLift N p i x)
    ((rawCoefficientSpace N p).sub_mem (rawFeature_mem N p x)
      ((rawCoefficientSpace N p).sum_mem (fun i _ =>
        (rawCoefficientSpace N p).smul_mem _ (zonalKernelLift_mem N p i x))))
  intro y hy
  rw [inner_sub_left, rawFeature_inner, sum_inner]
  simp_rw [real_inner_smul_left, zonalKernelLift_sphere hN p _ x y hx hy]
  have he : (∑ i : Fin (p/2+1),
      ((N : ℝ)^p*gammaWeight N p i.val)*zonal N (p-2*i.val) (overlap x y)) =
      (N : ℝ)^p * ∑ i : Fin (p/2+1),
        gammaWeight N p i.val*zonal N (p-2*i.val) (overlap x y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Fin.sum_univ_eq_sum_range (fun j : ℕ =>
    gammaWeight N p j*zonal N (p-2*j) (overlap x y)), ← power_expansion hN p]
  unfold overlap
  rw [div_pow]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  field_simp
  ring

def entranceSphere (N : ℕ) := {x : Vector N // ‖x‖^2 = (N : ℝ)}

/-- The genuine coefficient subspace for a spherical harmonic sector. -/
def harmonicSectorSubspace (N p : ℕ) (i : Fin (p/2+1)) :
    Submodule ℝ (EuclideanSpace ℝ (TensorIndex N p)) := by
  exact Submodule.span ℝ
    (Set.range (fun x : entranceSphere N => zonalKernelLift N p i x.val))

/-- Actual projected coefficient feature, with the original Hamiltonian
normalization and amplitude. It is defined on the whole ambient space. -/
def harmonicSectorFeature (N p : ℕ) (c : ℝ) (i : Fin (p/2+1)) (x : Vector N) :
    EuclideanSpace ℝ (TensorIndex N p) := by
  exact Real.sqrt c • (normalization N p •
    (((N : ℝ)^p*gammaWeight N p i.val) • zonalKernelLift N p i x))

/-- The actual spherical harmonic field of the original ordered tensor. -/
def harmonicSector (N p : ℕ) (c : ℝ) (i : Fin (p/2+1))
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) : ℝ :=
  inner ℝ (harmonicSectorFeature N p c i x) (WithLp.toLp 2 J)

private theorem rawSector_projection {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    (i : Fin (p/2+1)) (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    (harmonicSectorSubspace N p i).starProjection (rawFeature N p x) =
      ((N : ℝ)^p*gammaWeight N p i.val) • zonalKernelLift N p i x := by
  exact projection_of_orthogonal_feature_sum
    (fun z : entranceSphere N => rawFeature N p z.val)
    (fun j (z : entranceSphere N) => zonalKernelLift N p j z.val)
    (fun j => (N : ℝ)^p*gammaWeight N p j.val)
    (fun z => zonalKernelLift_reconstruction hN hp z.val z.property)
    (fun j k hjk z w => zonalKernelLift_orthogonal hN p j k hjk z.val w.val)
    i ⟨x,hx⟩

/-- All sectors are actual orthogonal projections of the original tensor
feature, including every positive degree and the constant degree. -/
theorem harmonicSectorFeature_projection {N p : ℕ} (hN : 3 ≤ N)
    (hp : 1 ≤ p) (c : ℝ) (i : Fin (p/2+1)) (x : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) :
    (harmonicSectorSubspace N p i).starProjection (pureCoefficientFeature N p c x) =
      harmonicSectorFeature N p c i x := by
  change (harmonicSectorSubspace N p i).starProjection
    (Real.sqrt c • (normalization N p • rawFeature N p x)) = _
  rw [map_smul, map_smul, rawSector_projection hN hp i x hx]
  rfl

/-- Orthogonality is proved for the genuine coefficient subspaces, with
no harmonic-space hypothesis. -/
theorem harmonicSectorSubspaces_orthogonal {N : ℕ} (hN : 3 ≤ N) (p : ℕ) :
    Pairwise (fun i j : Fin (p/2+1) =>
      harmonicSectorSubspace N p i ⟂ harmonicSectorSubspace N p j) :=
  featureSpans_orthogonal
    (fun i (x : entranceSphere N) => zonalKernelLift N p i x.val)
    (fun i j hij x y => zonalKernelLift_orthogonal hN p i j hij x.val y.val)

/-- Every projected harmonic feature is a smooth polynomial extension. -/
theorem harmonicSectorFeature_contDiff (N p : ℕ) (c : ℝ) (i : Fin (p/2+1)) :
    ContDiff ℝ ⊤ (harmonicSectorFeature N p c i) :=
  (((zonalKernelLift_contDiff N p i).const_smul _).const_smul _).const_smul _

/-- Literal zonal Gram identity for every actual harmonic sector. -/
theorem harmonicSectorFeature_inner {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    {c : ℝ} (hc : 0 ≤ c) (i : Fin (p/2+1)) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) :
    inner ℝ (harmonicSectorFeature N p c i x) (harmonicSectorFeature N p c i y) =
      (N : ℝ)*c*gammaWeight N p i.val*zonal N (p-2*i.val) (overlap x y) := by
  have hg := gram_of_orthogonal_feature_sum
    (fun z : entranceSphere N => rawFeature N p z.val)
    (fun j (z : entranceSphere N) => zonalKernelLift N p j z.val)
    (fun j => (N : ℝ)^p*gammaWeight N p j.val)
    (fun j (z w : entranceSphere N) => zonal N (p-2*j.val) (overlap z.val w.val))
    (fun z => zonalKernelLift_reconstruction hN hp z.val z.property)
    (fun j k hjk z w => zonalKernelLift_orthogonal hN p j k hjk z.val w.val)
    (fun j z w => zonalKernelLift_sphere hN p j z.val w.val z.property w.property)
    i ⟨x,hx⟩ ⟨y,hy⟩
  unfold harmonicSectorFeature
  rw [real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_left, real_inner_smul_right, hg]
  have hscale : (normalization N p)^2*(N : ℝ)^p = (N : ℝ) := by
    rw [normalization_sq N p (by omega : 0 < N)]
    have hs := dimension_covariance_scale N p (by omega : 0 < N) hp (N : ℝ)
    simpa only [div_self (show (N : ℝ) ≠ 0 by positivity), one_pow, mul_one] using hs
  have hcscale := Real.sq_sqrt hc
  calc
    _ = (Real.sqrt c)^2 * ((normalization N p)^2*(N : ℝ)^p) *
        gammaWeight N p i.val*zonal N (p-2*i.val) (overlap x y) := by ring
    _ = _ := by rw [hcscale,hscale]; ring




/-- The projected features commute with the actual tensor rotation. -/
theorem harmonicSectorFeature_rotated (N p : ℕ) (c : ℝ) (i : Fin (p/2+1))
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (x : Vector N) :
    SphericalAging.TensorOrthogonalAction.action U (harmonicSectorFeature N p c i x) =
      harmonicSectorFeature N p c i (U x) := by
  unfold harmonicSectorFeature
  rw [map_smul, map_smul, map_smul, zonalKernelLift_rotated]

/-- Rotation covariance holds sample by sample for the original disorder. -/
theorem harmonicSector_rotated (N p : ℕ) (c : ℝ) (i : Fin (p/2+1))
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    harmonicSector N p c i (SphericalAging.TensorHamiltonianRotation.rotatedDisorder U J)
      (U x) = harmonicSector N p c i J x := by
  unfold harmonicSector
  change inner ℝ (harmonicSectorFeature N p c i (U x))
    (SphericalAging.TensorOrthogonalAction.action U (WithLp.toLp 2 J)) = _
  rw [← harmonicSectorFeature_rotated]
  exact (SphericalAging.TensorOrthogonalAction.action U).inner_map_map _ _

/-- Every constructed sector has exactly its printed homogeneous degree. -/
theorem harmonicSector_homogeneous (N p : ℕ) (c : ℝ) (i : Fin (p/2+1))
    (J : SphericalAging.FiniteModel.Disorder N p) (r : ℝ) (x : Vector N) :
    harmonicSector N p c i J (r • x) = r^(p-2*i.val)*harmonicSector N p c i J x := by
  unfold harmonicSector harmonicSectorFeature
  rw [zonalKernelLift_homogeneous]
  simp only [smul_smul, real_inner_smul_left]
  ring

/-- The ambient homogeneous extension is harmonic everywhere. -/
theorem harmonicSector_laplacian {N : ℕ} (hN : 3 ≤ N) (p : ℕ) (c : ℝ)
    (i : Fin (p/2+1)) (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N) :
    Δ (harmonicSector N p c i J) x = 0 := by
  have he : harmonicSector N p c i J =
      (Real.sqrt c*normalization N p*((N : ℝ)^p*gammaWeight N p i.val)) •
        (fun y => inner ℝ (zonalKernelLift N p i y) (WithLp.toLp 2 J)) := by
    funext y
    simp only [harmonicSector, harmonicSectorFeature, Pi.smul_apply, smul_eq_mul,
      real_inner_smul_left]
    ring
  rw [he, InnerProductSpace.laplacian_smul _
    (((zonalKernelLift_contDiff N p i).inner ℝ contDiff_const).contDiffAt.of_le (by simp)),
    zonalKernelLift_harmonic_evaluation hN p i (WithLp.toLp 2 J) x, smul_zero]

/-- Each sample is an actual homogeneous harmonic polynomial. -/
theorem harmonicSector_harmonic {N : ℕ} (hN : 3 ≤ N) (p : ℕ) (c : ℝ)
    (i : Fin (p/2+1)) (J : SphericalAging.FiniteModel.Disorder N p) :
    InnerProductSpace.HarmonicOnNhd (harmonicSector N p c i J) Set.univ := by
  have hf : ContDiff ℝ 2 (harmonicSector N p c i J) :=
    ((harmonicSectorFeature_contDiff N p c i).inner ℝ contDiff_const).of_le (by simp)
  intro x _
  exact ⟨hf.contDiffAt, Filter.Eventually.of_forall
    (fun y => harmonicSector_laplacian hN p c i J y)⟩

/-- Exact reconstruction on the physical sphere. -/
theorem harmonicSector_sum {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    (c : ℝ) (J : SphericalAging.FiniteModel.Disorder N p) (x : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) :
    (∑ i : Fin (p/2+1), harmonicSector N p c i J x) =
      Real.sqrt c*Hamiltonian N p J x := by
  rw [← pureCoefficientFeature_field]
  change (∑ i : Fin (p/2+1),
    inner ℝ (harmonicSectorFeature N p c i x) (WithLp.toLp 2 J)) =
      inner ℝ (Real.sqrt c • (normalization N p • rawFeature N p x)) (WithLp.toLp 2 J)
  rw [zonalKernelLift_reconstruction hN hp x hx]
  simp only [Finset.smul_sum, sum_inner]
  rfl

/-- All sector evaluations are jointly Gaussian under the original tensor law. -/
theorem harmonicSector_jointGaussian (N p : ℕ) (c : ℝ)
    {T : Type*} [Fintype T] (x : T → Vector N) :
    HasGaussianLaw (fun J : SphericalAging.FiniteModel.Disorder N p =>
      fun q : Fin (p/2+1) × T => harmonicSector N p c q.1 J (x q.2))
      (SphericalAging.FiniteModel.disorderLaw N p) := by
  have h := (ordered_tensor_hasLaw N p).hasGaussianLaw.map_fun
    (ContinuousLinearMap.pi (fun q : Fin (p/2+1) × T =>
      innerSL ℝ (harmonicSectorFeature N p c q.1 (x q.2))))
  change HasGaussianLaw (fun J : SphericalAging.FiniteModel.Disorder N p =>
    fun q : Fin (p/2+1) × T =>
      inner ℝ (harmonicSectorFeature N p c q.1 (x q.2)) (WithLp.toLp 2 J))
    (SphericalAging.FiniteModel.disorderLaw N p) at h
  exact h

/-- Every genuine sector is centered. -/
theorem harmonicSector_mean (N p : ℕ) (c : ℝ) (i : Fin (p/2+1)) (x : Vector N) :
    (∫ J, harmonicSector N p c i J x ∂SphericalAging.FiniteModel.disorderLaw N p) = 0 := by
  exact ((ordered_tensor_hasLaw N p).integral_comp
    (show AEStronglyMeasurable (innerSL ℝ (harmonicSectorFeature N p c i x))
      (stdGaussian (EuclideanSpace ℝ (TensorIndex N p))) by fun_prop)).trans
        (integral_strongDual_stdGaussian _)

/-- Literal zonal covariance for every constructed harmonic sector. -/
theorem harmonicSector_covariance {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    {c : ℝ} (hc : 0 ≤ c) (i : Fin (p/2+1)) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) :
    cov[fun J => harmonicSector N p c i J x, fun J => harmonicSector N p c i J y;
      SphericalAging.FiniteModel.disorderLaw N p] =
      (N : ℝ)*c*gammaWeight N p i.val*zonal N (p-2*i.val) (overlap x y) := by
  unfold harmonicSector
  rw [tensor_inner_covariance, harmonicSectorFeature_inner hN hp hc i x y hx hy]

/-- The printed second-moment identity holds for every actual sector. -/
theorem harmonicSector_secondMoment {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    {c : ℝ} (hc : 0 ≤ c) (i : Fin (p/2+1)) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) :
    (∫ J, harmonicSector N p c i J x*harmonicSector N p c i J y
      ∂SphericalAging.FiniteModel.disorderLaw N p) =
      (N : ℝ)*c*gammaWeight N p i.val*zonal N (p-2*i.val) (overlap x y) := by
  have hgx : HasGaussianLaw (fun J => harmonicSector N p c i J x)
      (SphericalAging.FiniteModel.disorderLaw N p) :=
    (ordered_tensor_hasLaw N p).hasGaussianLaw.map_fun
      (innerSL ℝ (harmonicSectorFeature N p c i x))
  have hgy : HasGaussianLaw (fun J => harmonicSector N p c i J y)
      (SphericalAging.FiniteModel.disorderLaw N p) :=
    (ordered_tensor_hasLaw N p).hasGaussianLaw.map_fun
      (innerSL ℝ (harmonicSectorFeature N p c i y))
  have hh := harmonicSector_covariance hN hp hc i x y hx hy
  rw [covariance_eq_sub hgx.memLp_two hgy.memLp_two,
    harmonicSector_mean, harmonicSector_mean, zero_mul, sub_zero] at hh
  simpa only [Pi.mul_apply] using hh


private theorem harmonicSector_eq_projected {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p)
    (c : ℝ) (i : Fin (p/2+1)) (J : SphericalAging.FiniteModel.Disorder N p)
    (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    harmonicSector N p c i J x =
      inner ℝ (pureCoefficientFeature N p c x)
        ((harmonicSectorSubspace N p i).starProjection (WithLp.toLp 2 J)) := by
  rw [← (harmonicSectorSubspace N p i).inner_starProjection_left_eq_right,
    harmonicSectorFeature_projection hN hp c i x hx]
  rfl

/-- Independence of all complete sector fields under the original
ordered-tensor Gaussian law, including the constant sector. -/
theorem harmonicSectors_independent {N p : ℕ} (hN : 3 ≤ N) (hp : 1 ≤ p) (c : ℝ) :
    iIndepFun (fun i : Fin (p/2+1) =>
      fun J : SphericalAging.FiniteModel.Disorder N p =>
        fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} => harmonicSector N p c i J x.val)
      (SphericalAging.FiniteModel.disorderLaw N p) := by
  let V := harmonicSectorSubspace N p
  have hG := (ordered_tensor_hasLaw N p).hasGaussianLaw.map_fun
    (ContinuousLinearMap.pi (fun i : Fin (p/2+1) => (V i).starProjection))
  have hproj : iIndepFun (fun i : Fin (p/2+1) =>
      fun J : SphericalAging.FiniteModel.Disorder N p =>
        (V i).starProjection (WithLp.toLp 2 J))
      (SphericalAging.FiniteModel.disorderLaw N p) := by
    apply hG.iIndepFun_of_covariance_inner
    intro i j hij a b
    change cov[fun J => inner ℝ a ((V i).starProjection (WithLp.toLp 2 J)),
      fun J => inner ℝ b ((V j).starProjection (WithLp.toLp 2 J));
      SphericalAging.FiniteModel.disorderLaw N p] = 0
    have ha : (fun J : SphericalAging.FiniteModel.Disorder N p =>
        inner ℝ a ((V i).starProjection (WithLp.toLp 2 J))) =
        fun J => inner ℝ ((V i).starProjection a) (WithLp.toLp 2 J) := by
      funext J
      exact ((V i).inner_starProjection_left_eq_right a _).symm
    have hb : (fun J : SphericalAging.FiniteModel.Disorder N p =>
        inner ℝ b ((V j).starProjection (WithLp.toLp 2 J))) =
        fun J => inner ℝ ((V j).starProjection b) (WithLp.toLp 2 J) := by
      funext J
      exact ((V j).inner_starProjection_left_eq_right b _).symm
    rw [ha, hb, tensor_inner_covariance]
    exact (harmonicSectorSubspaces_orthogonal hN p hij).inner_eq
      ((V i).starProjection_apply_mem a) ((V j).starProjection_apply_mem b)
  have hf := hproj.comp
    (fun _ z => fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
      inner ℝ (pureCoefficientFeature N p c x.val) z)
    (fun _ => Measurable.of_eval (fun _ => by fun_prop))
  apply hf.congr
  intro i
  exact Filter.Eventually.of_forall fun J => by
    funext x
    dsimp only [Function.comp_def]
    exact (harmonicSector_eq_projected hN hp c i J x.val x.property).symm

-- PUBLIC_SECTORS_END

-- MIXTURE_HELPERS_BEGIN

private theorem iIndepFun_comp_hasLaw {ι Ω Θ : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Θ] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] {μ : Measure Ω} {ν : Measure Θ}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Y : Θ → Ω) (hY : Measurable Y) (hLaw : HasLaw Y μ ν)
    (f : (i : ι) → Ω → β i) (hf : ∀ i, Measurable (f i)) (hI : iIndepFun f μ) :
    iIndepFun (fun i z => f i (Y z)) ν := by
  change iIndepFun (fun i => f i ∘ Y) ν
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun i => ((hf i).comp hY).aemeasurable)]
  change ν.map (fun z i => f i (Y z)) = Measure.pi (fun i => ν.map (fun z => f i (Y z)))
  have hmap : ν.map (fun z i => f i (Y z)) = μ.map (fun z i => f i z) := by
    have h := (Measure.map_map (μ := ν) (Measurable.of_eval hf) hY).symm
    simpa only [hLaw.map_eq, Function.comp_def] using h
  have hmarg (i : ι) : ν.map (fun z => f i (Y z)) = μ.map (f i) := by
    have h := (Measure.map_map (μ := ν) (hf i) hY).symm
    simpa only [hLaw.map_eq, Function.comp_def] using h
  rw [hmap]
  simp_rw [hmarg]
  exact hI.map_fun_eq_pi_map (fun i => (hf i).aemeasurable)

/-- All spherical harmonic sectors of all original mixture degrees are
independent simultaneously, as complete fields on the physical sphere.
The probability law is the actual original product disorder law. -/
theorem mixture_harmonicSectors_independent {N P : ℕ} (hN : 3 ≤ N)
    (c : Degree P → ℝ) :
    iIndepFun (fun a : Σ p : Degree P, Fin (p.val.val/2+1) =>
      fun J : SphericalModel.Disorder N P =>
        fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
          harmonicSector N a.1.val.val (c a.1) a.2 (J a.1) x.val)
      (SphericalModel.disorderLaw N P) := by
  let X (p : Degree P) (i : Fin (p.val.val/2+1)) (J : SphericalModel.Disorder N P) :=
    fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
      harmonicSector N p.val.val (c p) i (J p) x.val
  have hm (p : Degree P) (i : Fin (p.val.val/2+1)) : Measurable (X p i) := by
    apply Measurable.of_eval
    intro x
    dsimp only [X, harmonicSector]
    fun_prop
  have hblock : iIndepFun (fun p (J : SphericalModel.Disorder N P) => fun i => X p i J)
      (SphericalModel.disorderLaw N P) := by
    have h := (SphericalModel.independent_degree_blocks N P).comp
      (fun p (J : SphericalAging.FiniteModel.Disorder N p.val.val) =>
        fun i : Fin (p.val.val/2+1) =>
          fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
            harmonicSector N p.val.val (c p) i J x.val)
      (fun _ => Measurable.of_eval (fun _ => Measurable.of_eval (fun _ => by
        unfold harmonicSector
        fun_prop)))
    simpa only [Function.comp_def, X] using h
  have hsector (p : Degree P) : iIndepFun (fun i => X p i)
      (SphericalModel.disorderLaw N P) := by
    have hp : 1 ≤ p.val.val := by have := p.property; omega
    have h := iIndepFun_comp_hasLaw
      (fun J : SphericalModel.Disorder N P => J p) (measurable_pi_apply p)
      (SphericalModel.degree_block_hasLaw p)
      (fun i (J : SphericalAging.FiniteModel.Disorder N p.val.val) =>
        fun x : {x : Vector N // ‖x‖^2 = (N : ℝ)} =>
          harmonicSector N p.val.val (c p) i J x.val)
      (fun _ => Measurable.of_eval (fun _ => by unfold harmonicSector; fun_prop))
      (harmonicSectors_independent hN hp (c p))
    exact h
  exact iIndepFun_uncurry hm hblock hsector

private def mixtureSectorObservation {N P : ℕ} (c : Degree P → ℝ) (p : Degree P)
    (i : Fin (p.val.val/2+1)) (x : Vector N) : SphericalModel.Disorder N P →L[ℝ] ℝ :=
  (∑ I : TensorIndex N p.val.val,
    (harmonicSectorFeature N p.val.val (c p) i x I) • ContinuousLinearMap.proj I).comp
      (ContinuousLinearMap.proj p)

private theorem mixtureSectorObservation_apply {N P : ℕ} (c : Degree P → ℝ) (p : Degree P)
    (i : Fin (p.val.val/2+1)) (x : Vector N) (J : SphericalModel.Disorder N P) :
    mixtureSectorObservation c p i x J = harmonicSector N p.val.val (c p) i (J p) x := by
  simp [mixtureSectorObservation, harmonicSector, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- Every finite family of harmonic-sector evaluations across arbitrary
original degrees is jointly Gaussian under the actual mixture disorder. -/
theorem mixture_harmonicSector_jointGaussian {N P : ℕ} (c : Degree P → ℝ)
    {T : Type*} [Fintype T] (a : T → Σ p : Degree P, Fin (p.val.val/2+1))
    (x : T → Vector N) :
    HasGaussianLaw (fun J : SphericalModel.Disorder N P => fun t =>
      harmonicSector N (a t).1.val.val (c (a t).1) (a t).2 (J (a t).1) (x t))
      (SphericalModel.disorderLaw N P) := by
  have h := (SphericalModel.disorder_hasGaussianLaw N P).map_fun
    (ContinuousLinearMap.pi (fun t => mixtureSectorObservation c (a t).1 (a t).2 (x t)))
  change HasGaussianLaw (fun J : SphericalModel.Disorder N P =>
    fun t => mixtureSectorObservation c (a t).1 (a t).2 (x t) J)
      (SphericalModel.disorderLaw N P) at h
  simpa only [mixtureSectorObservation_apply] using h

/-- The literal original-mixture expectation of each harmonic sector is zero. -/
theorem mixture_harmonicSector_mean {N P : ℕ} (c : Degree P → ℝ) (p : Degree P)
    (i : Fin (p.val.val/2+1)) (x : Vector N) :
    (∫ J : SphericalModel.Disorder N P, harmonicSector N p.val.val (c p) i (J p) x
      ∂SphericalModel.disorderLaw N P) = 0 := by
  have h := (SphericalModel.degree_block_hasLaw p).integral_comp
    (show AEStronglyMeasurable
      (fun J : SphericalAging.FiniteModel.Disorder N p.val.val =>
        harmonicSector N p.val.val (c p) i J x)
      (SphericalAging.FiniteModel.disorderLaw N p.val.val) by
        unfold harmonicSector
        fun_prop)
  exact h.trans (harmonicSector_mean N p.val.val (c p) i x)

/-- The printed zonal second moment holds in the original joint mixture
law, with the original degree block and its literal Gamma coefficient. -/
theorem mixture_harmonicSector_secondMoment {N P : ℕ} (hN : 3 ≤ N)
    (c : Degree P → ℝ) (p : Degree P) (hc : 0 ≤ c p)
    (i : Fin (p.val.val/2+1)) (x y : Vector N)
    (hx : ‖x‖^2 = (N : ℝ)) (hy : ‖y‖^2 = (N : ℝ)) :
    (∫ J : SphericalModel.Disorder N P,
      harmonicSector N p.val.val (c p) i (J p) x * harmonicSector N p.val.val (c p) i (J p) y
        ∂SphericalModel.disorderLaw N P) =
      (N : ℝ)*(c p)*gammaWeight N p.val.val i.val*
        zonal N (p.val.val-2*i.val) (overlap x y) := by
  have h := (SphericalModel.degree_block_hasLaw p).integral_comp
    (show AEStronglyMeasurable
      (fun J : SphericalAging.FiniteModel.Disorder N p.val.val =>
        harmonicSector N p.val.val (c p) i J x * harmonicSector N p.val.val (c p) i J y)
      (SphericalAging.FiniteModel.disorderLaw N p.val.val) by
        unfold harmonicSector
        fun_prop)
  have hp : 1 ≤ p.val.val := by have := p.property; omega
  exact h.trans (harmonicSector_secondMoment hN hp hc i x y hx hy)

-- MIXTURE_HELPERS_END

-- FULL_EVENT_BEGIN

namespace FullEvent

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open SourceEntranceRegularityLiteral SourceEntranceGoodEvent SourceEntranceHarmonicFinal
open SourceEntranceHarmonic SourceEntranceRegressionBoundary WholeFieldRegression
open SphericalPosteriorGradientIndependence EntranceLatitudeTangentObservable
open SphericalAging.OrthogonalGaussianDisclosure
open SphericalLatitudeTensorMoments FiniteWickPairings PairedTensorProjectionFeatures
open PureTensorJetBounds GaussianCompactMaximum GaussianSharpAbsoluteMaximum
open scoped BigOperators RealInnerProductSpace NNReal ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem latitudePairingEnvelope_sharp_tail {n p : ℕ} (hn : 1 ≤ n)
    (S : Finset (Fin p)) (L : List (Fin p × Fin p)) (hL : ValidPairing S L)
    (hj : 0 < L.length) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p
      {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
        latitudePairingEnvelope n p S L hL J} ≤
      ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
  have ht := originalPairedEnvelope_sharp_tail (by omega : 2 ≤ n+1)
    (Finset.univ\S).card L.length hj
  have hm : MeasurableSet {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
      originalPairedEnvelope (n+1) (Finset.univ\S).card L.length J} := by
    apply (isClosed_le continuous_const _).measurableSet
    exact (pairedGaussianEnvelope_lipschitz (by omega) (Finset.univ\S).card L.length hj).continuous.comp
      (by fun_prop)
  have he := (pairingReindexedTensor_measurePreserving (N := n+1) S L hL).hasLaw.measure_eq hm
  change SphericalAging.FiniteModel.disorderLaw (n+1) p
    {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.length : ℝ))+1 ≤
      originalPairedEnvelope (n+1) (Finset.univ\S).card L.length
        (pairingReindexedTensor S L hL J)} ≤ _
  rw [he]
  exact ht

private theorem measure_exists_list_le {Ω ι : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (T : List ι) (A : ι → Set Ω) (c : ℝ≥0∞)
    (hA : ∀ a ∈ T, ν (A a) ≤ c) :
    ν {ω | ∃ a ∈ T, ω ∈ A a} ≤ (T.length : ℝ≥0∞)*c := by
  induction T with
  | nil => simp
  | cons a T ih =>
    have he : {ω | ∃ b ∈ a::T, ω ∈ A b} = A a ∪ {ω | ∃ b ∈ T, ω ∈ A b} := by
      ext ω
      simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union]
      aesop
    rw [he]
    apply (measure_union_le _ _).trans
    have h := add_le_add (hA a (by simp)) (ih (fun b hb => hA b (by simp [hb])))
    simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using h

private theorem latitudeCorrectionBadBanks_sharp_tail {n p : ℕ} (hn : 1 ≤ n) :
    SphericalAging.FiniteModel.disorderLaw (n+1) p (latitudeCorrectionBadBanks n p) ≤
      (latitudeCorrectionBankCount p : ℝ≥0∞)*
        ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
  unfold latitudeCorrectionBadBanks
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ S ∈ ((Finset.univ : Finset (Fin p)).powerset.erase ∅),
        ((labeledWickPairings S).length : ℝ≥0∞)*
          ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
      apply Finset.sum_le_sum
      intro S hS
      have he := measure_exists_list_le (SphericalAging.FiniteModel.disorderLaw (n+1) p)
        (labeledWickPairings S).attach
        (fun L => {J | 2*Real.sqrt (((Finset.univ\S).card : ℝ)+4*(L.val.length : ℝ))+1 ≤
          latitudePairingEnvelope n p S L.val (labeledWickPairings_valid S L.val L.property) J})
        (ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2))) (by
          intro L _
          exact latitudePairingEnvelope_sharp_tail hn S L.val
            (labeledWickPairings_valid S L.val L.property)
            (nonempty_Wick_pairing_length_pos (Finset.mem_erase.mp hS).1 L.property))
      simpa only [List.length_attach, Set.mem_ofPred_eq] using he
    _ = _ := by rw [← Finset.sum_mul]; simp only [latitudeCorrectionBankCount, Nat.cast_sum]

private theorem regularDisorder_sharp_tail {N P : ℕ} (hN : 2 ≤ N) (hP : 2 ≤ P) :
    (SphericalModel.disorderLaw N P).real (regularDisorder (N := N) (P := P))ᶜ ≤ Real.exp (-2*(N : ℝ)) := by
  classical
  let : Nonempty (Degree P) := ⟨⟨⟨2, by omega⟩, by change 2 ≤ (2 : ℕ); omega⟩⟩
  let m : ℝ := Fintype.card (Degree P)
  have hm : 1 ≤ m := by
    have hcard : 0 < Fintype.card (Degree P) := Fintype.card_pos
    dsimp [m]
    exact_mod_cast hcard
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hbad : (regularDisorder (N := N) (P := P))ᶜ =
      ⋃ p : Degree P, {J : SphericalModel.Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} := by
    ext J
    simp [regularDisorder, not_forall, not_le]
  have hblock (p : Degree P) :
      (SphericalModel.disorderLaw N P).real {J : SphericalModel.Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} ≤
      2*Real.exp (-(N : ℝ)*(m+1)^2) := by
    rw [(degree_block_hasLaw p).measureReal_eq
      (measurableSet_lt measurable_const (GaussianLandscape.landscapeNorm_continuous N p.val.val).measurable)]
    have hthreshold : GaussianLandscape.landscapeThreshold p.val.val ≤ blockThreshold p := by
      unfold blockThreshold
      have hm0 : (0 : ℝ) ≤ Fintype.card (Degree P) := Nat.cast_nonneg _
      linarith
    have ht := GaussianLandscape.landscape_tail_dimension
      (N := N) (p := p.val.val) (by omega) (by omega) hthreshold
    have hb := (GaussianLandscape.landscapeThreshold_pos p.val.val).le
    have hs : 16*(m+1)^2 ≤ blockThreshold p^2 := by
      change 16*(m+1)^2 ≤ (GaussianLandscape.landscapeThreshold p.val.val+4*(m+1))^2
      nlinarith [mul_nonneg hb (show 0 ≤ m+1 by linarith)]
    exact ht.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg N) (sub_nonneg.mpr hs)]))
      (by norm_num))
  rw [hbad]
  calc
    _ ≤ ∑ p : Degree P, (SphericalModel.disorderLaw N P).real {J : SphericalModel.Disorder N P |
        blockThreshold p < GaussianLandscape.landscapeNorm N p.val.val (J p)} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p : Degree P, 2*Real.exp (-(N : ℝ)*(m+1)^2) :=
      Finset.sum_le_sum (fun p _ => hblock p)
    _ = (2*m)*Real.exp (-(N : ℝ)*(m+1)^2) := by simp [m]; ring
    _ ≤ Real.exp (2*m)*Real.exp (-(N : ℝ)*(m+1)^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (2*m)]
    _ = Real.exp (2*m-(N : ℝ)*(m+1)^2) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-2*(N : ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg N) (show 0 ≤ m^2-1 by nlinarith),
        mul_nonneg (sub_nonneg.mpr hNr) (show 0 ≤ m by linarith)]

private theorem dimension_div_sqrt_pow {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (N : ℝ)/Real.sqrt ((N : ℝ)^k) = (N : ℝ)^(1-(k : ℝ)/2) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  rw [Real.rpow_sub hNr, Real.rpow_one]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
  congr 1
  ring

private theorem originalLatitudeMeanGood_spare_failure {n : ℕ} (hn : 1 ≤ n)
    (μ : FiniteMixture) :
    (SphericalModel.disorderLaw (n+1) μ.maxDegree).real (originalLatitudeMeanGood n μ)ᶜ ≤
      (1+4*(originalLatitudeBankCount μ : ℝ))*Real.exp (-2*((n+1 : ℕ) : ℝ)) := by
  classical
  obtain ⟨p,hp⟩ := μ.support_nonempty
  have hP : 2 ≤ μ.maxDegree := (μ.degree_ge_two hp).trans (μ.degree_bounds hp).2
  have he : (originalLatitudeMeanGood n μ)ᶜ =
      (regularDisorder (N := n+1) (P := μ.maxDegree))ᶜ ∪
      ⋃ p : Degree μ.maxDegree, {J : SphericalModel.Disorder (n+1) μ.maxDegree |
        J p ∈ latitudeCorrectionBadBanks n p.val.val} := by
    ext J
    simp only [originalLatitudeMeanGood, Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_union, Set.mem_iUnion, not_and_or, not_forall, not_not]
  have hb : SphericalModel.disorderLaw (n+1) μ.maxDegree
      (⋃ p : Degree μ.maxDegree, {J : SphericalModel.Disorder (n+1) μ.maxDegree |
        J p ∈ latitudeCorrectionBadBanks n p.val.val}) ≤
      (originalLatitudeBankCount μ : ℝ≥0∞)*ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
    apply (measure_iUnion_fintype_le _ _).trans
    calc
      _ ≤ ∑ p : Degree μ.maxDegree, (latitudeCorrectionBankCount p.val.val : ℝ≥0∞)*
          ENNReal.ofReal (4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2)) := by
        apply Finset.sum_le_sum
        intro p _
        have heq : SphericalModel.disorderLaw (n+1) μ.maxDegree {J | J p ∈ latitudeCorrectionBadBanks n p.val.val} =
            SphericalAging.FiniteModel.disorderLaw (n+1) p.val.val (latitudeCorrectionBadBanks n p.val.val) := by
          convert (degree_block_hasLaw p).measure_eq (latitudeCorrectionBadBanks_measurable hn) using 1
          all_goals congr 1
        rw [heq]
        exact latitudeCorrectionBadBanks_sharp_tail hn
      _ = _ := by rw [← Finset.sum_mul]; simp only [originalLatitudeBankCount, Nat.cast_sum]
  have hbr := ENNReal.toReal_mono (by finiteness) hb
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*Real.exp (-9*((n+1 : ℕ) : ℝ)/2))] at hbr
  rw [he]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (regularDisorder_sharp_tail (by omega) hP) hbr).trans
  have he := Real.exp_le_exp.mpr (show -9*((n+1 : ℕ) : ℝ)/2 ≤ -2*((n+1 : ℕ) : ℝ) by have h : (0 : ℝ) ≤ (n+1 : ℕ) := Nat.cast_nonneg _; linarith)
  nlinarith [mul_le_mul_of_nonneg_left he (Nat.cast_nonneg (originalLatitudeBankCount μ))]

private theorem mass_half_of_failure {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E : Set A} (hE : MeasurableSet E)
    {N : ℕ} (hN : 2 ≤ N) (hfail : P.real Eᶜ ≤ Real.exp (-(N : ℝ))) :
    (1/2 : ℝ) ≤ P.real E := by
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp (-(N : ℝ)) ≤ 1/2 := by
    rw [Real.exp_neg]
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
    linarith [Real.add_one_le_exp (N : ℝ)]
  have hs := measureReal_add_measureReal_compl (μ := P) hE
  rw [probReal_univ] at hs
  linarith

private theorem zonal_uniform_chord_bound (ell : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (N : ℕ), 3 ≤ N → ∀ r : ℝ, |r| ≤ 1 →
      |zonal N ell r-1| ≤ D*(1-r) := by
  obtain ⟨A,hA,hderiv⟩ := zonal_derivative_bound ell
  let D := 1+2*A
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro N hN r hr
  have hderiv' (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) :
      ‖deriv (zonal N ell) t‖ ≤ D := by
    have ht' : |t| ≤ 1 := abs_le.mpr ht
    have hp : |t|^(ell-1) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht'
    have hi : (N : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by
      exact_mod_cast (show 1 ≤ N by omega))
    have h := hderiv N hN t ht'
    rw [Real.norm_eq_abs]
    dsimp [D]
    nlinarith
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t (_ : t ∈ Icc (-1 : ℝ) 1) =>
      ((contDiff_zonal N ell).differentiable (by simp)) t)
    hderiv' (convex_Icc (-1 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (-1 : ℝ) 1)
    (abs_le.mp hr)
  rw [zonal_at_one hN, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [(abs_le.mp hr).2] : r-1 ≤ 0)] at h
  nlinarith

/-- Standard Gaussian supremum control from the literal zonal Gram identity.
The comparison constant depends only on the harmonic degree.  Continuity,
the mean bound, and the exponential tail are proved from that deterministic
identity; no analytic literature interface is assumed.  Instantiating this
lemma for every original harmonic sector still requires constructing those
features and proving their Gram identities. -/
private theorem zonalFeature_supremum_upper_tail (ell : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 3 ≤ N →
      ∀ {ι : Type*} [Fintype ι] [DecidableEq ι]
        (a : UnitSphere N → EuclideanSpace ℝ ι) {b : ℝ}, 0 ≤ b →
        (∀ u v : UnitSphere N,
          inner ℝ (a u) (a v) = b^2*zonal N ell (inner ℝ (u : Vector N) (v : Vector N))) →
        Continuous a ∧
        (∫ g, absoluteSupremum a g ∂SYK.standardGaussianMeasureOnEuclidean ι) ≤
          C*b*Real.sqrt N ∧
        ∀ {s : ℝ}, 0 ≤ s →
          (SYK.standardGaussianMeasureOnEuclidean ι).real
            {g | (C+s)*b*Real.sqrt N < absoluteSupremum a g} ≤
              Real.exp (-s^2*(N : ℝ)/2) := by
  obtain ⟨D,hD,hchord⟩ := zonal_uniform_chord_bound ell
  have hD0 : 0 < D := by linarith
  have hP : 1 ≤ Real.sqrt D := (Real.le_sqrt (by norm_num) hD0.le).2 (by nlinarith)
  refine ⟨2*Real.sqrt D,by positivity,?_⟩
  intro N hN ι _ _ a b hb hgram
  let : NeZero N := ⟨by omega⟩
  have hnormsq (u : UnitSphere N) : ‖a u‖^2 = b^2 := by
    have h := hgram u u
    simpa only [real_inner_self_eq_norm_sq, unit_norm, one_pow,
      zonal_at_one hN, mul_one] using h
  have hnorm (u : UnitSphere N) : ‖a u‖ = b :=
    (sq_eq_sq₀ (norm_nonneg _) hb).mp (hnormsq u)
  have hinc (u v : UnitSphere N) :
      ‖a u-a v‖ ≤ b*Real.sqrt D*‖(u : Vector N)-(v : Vector N)‖ := by
    have hr : |inner ℝ (u : Vector N) (v : Vector N)| ≤ 1 := by
      simpa only [unit_norm, one_mul] using abs_real_inner_le_norm (u : Vector N) (v : Vector N)
    have hc := hchord N hN (inner ℝ (u : Vector N) (v : Vector N)) hr
    have hz : 1-zonal N ell (inner ℝ (u : Vector N) (v : Vector N)) ≤
        D*(1-inner ℝ (u : Vector N) (v : Vector N)) := by
      have hh := neg_le_abs (zonal N ell (inner ℝ (u : Vector N) (v : Vector N))-1)
      linarith
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hD0.le, norm_sub_sq_real,
      hnormsq, hnormsq, hgram, norm_sub_sq_real]
    simp only [unit_norm, one_pow]
    have h := mul_le_mul_of_nonneg_left hz (sq_nonneg b)
    nlinarith
  have hLip : LipschitzWith (b*Real.sqrt D).toNNReal a := by
    apply LipschitzWith.of_dist_le'
    intro u v
    change dist (a u) (a v) ≤ b*Real.sqrt D*dist (u : Vector N) (v : Vector N)
    simpa only [dist_eq_norm] using hinc u v
  have ha : Continuous a := hLip.continuous
  have hmean := expected_absoluteSupremum_le_twice a
    (fun u : UnitSphere N => (u : Vector N)) ha continuous_subtype_val
    (L := b*Real.sqrt D) (by positivity)
    (fun u => (hnorm u).le.trans (le_mul_of_one_le_right hb hP)) unit_norm hinc
  simp only [Fintype.card_fin] at hmean
  refine ⟨ha,by nlinarith [hmean],?_⟩
  intro s hs
  by_cases hb0 : b = 0
  · have hazero : a = fun _ => 0 := by
      funext u
      apply norm_eq_zero.mp
      simpa only [hb0] using hnorm u
    have hsup : absoluteSupremum a = fun _ => 0 := by
      funext g
      simp [absoluteSupremum, signedFeature, hazero]
    rw [hsup, hb0]
    simp only [mul_zero, zero_mul, lt_self_iff_false, Set.ofPred_false, measureReal_empty]
    positivity
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
    have hsupLip : LipschitzWith b.toNNReal (absoluteSupremum a) := by
      apply field_supremum_lipschitz
        (fun v : Bool × UnitSphere N => innerSL ℝ (signedFeature a v))
      intro v
      simpa only [innerSL_apply_norm, signedFeature, norm_smul, Real.norm_eq_abs,
        abs_sign, one_mul, hnorm] using (le_rfl : b ≤ b)
    have ht := GaussianNormConcentration.centered_lipschitz_upper_tail
      (absoluteSupremum a) hb hsupLip (s := s*b*Real.sqrt N) (by positivity)
    have hsub : {g | (2*Real.sqrt D+s)*b*Real.sqrt N < absoluteSupremum a g} ⊆
        {g | (∫ z, absoluteSupremum a z ∂SYK.standardGaussianMeasureOnEuclidean ι)+
          s*b*Real.sqrt N ≤ absoluteSupremum a g} := by
      intro g hg
      change (2*Real.sqrt D+s)*b*Real.sqrt N < absoluteSupremum a g at hg
      change _ ≤ absoluteSupremum a g
      nlinarith [hmean]
    apply (measureReal_mono hsub).trans (ht.trans_eq ?_)
    congr 1
    rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    field_simp

/-- The literal source-scale Gaussian envelope estimate for every coefficient
feature with the printed harmonic Gram kernel.  The constant is fixed before
the dimension and before the feature itself.  This is a proved consequence of
the deterministic Gram identity and the scalar Gamma-weight estimate, rather
than an assumed sector-concentration interface. -/
theorem zonalFeature_source_scale_upper_tail (p j : ℕ) (hj : 2*j ≤ p)
    {c : ℝ} (hc : 0 ≤ c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 3 ≤ N →
      ∀ (a : UnitSphere N → EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p)),
        (∀ u v : UnitSphere N,
          inner ℝ (a u) (a v) = (N : ℝ)*c*gammaWeight N p j*
            zonal N (p-2*j) (inner ℝ (u : Vector N) (v : Vector N))) →
        (SphericalAging.FiniteModel.disorderLaw N p).real
          {J | C*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a (WithLp.toLp 2 J)} ≤
            Real.exp (-2*(N : ℝ)) := by
  obtain ⟨A,hA,hweight⟩ := gammaWeights_bound_all_dimensions p
  obtain ⟨K,hK,hgaussian⟩ := zonalFeature_supremum_upper_tail (p-2*j)
  refine ⟨(K+2)*(Real.sqrt (c*A)+1),by positivity,?_⟩
  intro N hN a hgram
  let : NeZero N := ⟨by omega⟩
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hpow : 0 < (N : ℝ)^j := pow_pos hNr j
  have hvar : 0 ≤ (N : ℝ)*c*gammaWeight N p j :=
    mul_nonneg (mul_nonneg hNr.le hc) (gammaWeight_pos hN p j).le
  let b := Real.sqrt ((N : ℝ)*c*gammaWeight N p j)
  have hscale : b*Real.sqrt N ≤ (Real.sqrt (c*A)+1)*(N : ℝ)^(1-(j : ℝ)/2) := by
    have hw := (le_div_iff₀ hpow).mp (hweight N hN j hj)
    have hprod : (b*Real.sqrt N*Real.sqrt ((N : ℝ)^j))^2 ≤
        (Real.sqrt (c*A)*(N : ℝ))^2 := by
      dsimp [b]
      simp only [mul_pow, Real.sq_sqrt hvar, Real.sq_sqrt hNr.le,
        Real.sq_sqrt hpow.le, Real.sq_sqrt (mul_nonneg hc hA.le)]
      have h := mul_le_mul_of_nonneg_left hw (mul_nonneg (sq_nonneg (N : ℝ)) hc)
      nlinarith
    have hnorm : b*Real.sqrt N*Real.sqrt ((N : ℝ)^j) ≤ Real.sqrt (c*A)*(N : ℝ) := by
      nlinarith [show 0 ≤ Real.sqrt (c*A)*(N : ℝ) by positivity]
    have hdiv := (le_div_iff₀ (Real.sqrt_pos.2 hpow)).2 hnorm
    have hscale' : b*Real.sqrt N ≤ Real.sqrt (c*A)*(N : ℝ)^(1-(j : ℝ)/2) := by
      simpa only [mul_div_assoc, dimension_div_sqrt_pow (by omega : 0 < N)] using hdiv
    exact hscale'.trans (mul_le_mul_of_nonneg_right (by linarith)
      (Real.rpow_nonneg hNr.le _))
  obtain ⟨ha,_,htail⟩ := hgaussian hN a (show 0 ≤ b by dsimp [b]; positivity) (by
    intro u v
    dsimp [b]
    rw [Real.sq_sqrt hvar]
    exact hgram u v)
  have htail' := htail (s := 2) (by norm_num)
  have hbound : (K+2)*b*Real.sqrt N ≤
      ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) := by
    have h := mul_le_mul_of_nonneg_left hscale (show 0 ≤ K+2 by linarith)
    nlinarith
  have hsub : {g | ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a g} ⊆
      {g | (K+2)*b*Real.sqrt N < absoluteSupremum a g} := by
    intro g hg
    exact lt_of_le_of_lt hbound hg
  have hLcont : Continuous (fun v : Bool × UnitSphere N => innerSL ℝ (signedFeature a v)) :=
    (innerSL ℝ).continuous.comp (signedFeature_continuous a ha)
  obtain ⟨L,_,hL⟩ := exists_feature_bound _ hLcont
  have hcont : Continuous (absoluteSupremum a) := (field_supremum_lipschitz _ hL).continuous
  have hm : MeasurableSet
      {g | ((K+2)*(Real.sqrt (c*A)+1))*(N : ℝ)^(1-(j : ℝ)/2) < absoluteSupremum a g} :=
    (isOpen_lt continuous_const hcont).measurableSet
  have hLaw : HasLaw (WithLp.toLp 2 : SphericalAging.FiniteModel.Disorder N p →
      EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p))
      (SYK.standardGaussianMeasureOnEuclidean (SphericalAging.FiniteModel.TensorIndex N p))
      (SphericalAging.FiniteModel.disorderLaw N p) := ⟨by fun_prop,rfl⟩
  rw [hLaw.measureReal_eq hm]
  apply (measureReal_mono hsub).trans (htail'.trans_eq ?_)
  congr 1
  ring

private theorem physicalAxis_overlap {N : ℕ} (hN : 0 < N) (u v : UnitSphere N) :
    overlap (physicalAxis u) (physicalAxis v) = inner ℝ (u : Vector N) (v : Vector N) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  unfold overlap physicalAxis
  rw [real_inner_smul_left, real_inner_smul_right]
  calc
    _ = (Real.sqrt N*Real.sqrt N)*inner ℝ (u : Vector N) (v : Vector N)/(N : ℝ) := by ring
    _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg N)]; field_simp

/-- The actual absolute supremum of one original harmonic sector. -/
def harmonicSectorEnvelope (N p : ℕ) (c : ℝ) (i : Fin (p/2+1))
    (J : SphericalAging.FiniteModel.Disorder N p) : ℝ :=
  absoluteSupremum (fun u : UnitSphere N => harmonicSectorFeature N p c i (physicalAxis u))
    (WithLp.toLp 2 J)

private theorem harmonicSectorEnvelope_continuous {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (c : ℝ) (i : Fin (p/2+1)) : Continuous (harmonicSectorEnvelope N p c i) := by
  let : NeZero N := ⟨by omega⟩
  let a := fun u : UnitSphere N => harmonicSectorFeature N p c i (physicalAxis u)
  have ha : Continuous a := (harmonicSectorFeature_contDiff N p c i).continuous.comp
    (continuous_subtype_val.const_smul (Real.sqrt N))
  have hLcont : Continuous (fun v : Bool × UnitSphere N => innerSL ℝ (signedFeature a v)) :=
    (innerSL ℝ).continuous.comp (signedFeature_continuous a ha)
  obtain ⟨L,_,hL⟩ := exists_feature_bound _ hLcont
  have hF : Continuous (absoluteSupremum a) := (field_supremum_lipschitz _ hL).continuous
  exact hF.comp (by fun_prop)

private theorem harmonicSector_abs_le_envelope {N : ℕ} (hN : 1 ≤ N)
    (p : ℕ) (c : ℝ) (i : Fin (p/2+1)) (J : SphericalAging.FiniteModel.Disorder N p)
    (x : Vector N) (hx : ‖x‖^2 = (N : ℝ)) :
    |harmonicSector N p c i J x| ≤ harmonicSectorEnvelope N p c i J := by
  let : NeZero N := ⟨by omega⟩
  obtain ⟨u,hu⟩ := exists_unit_scale (by omega : 0 < N) x
  rw [LandscapeDerivatives.sphere_norm x hx] at hu
  rw [hu]
  apply norm_inner_le_absoluteSupremum
    (fun v : UnitSphere N => harmonicSectorFeature N p c i (physicalAxis v))
    ((harmonicSectorFeature_contDiff N p c i).continuous.comp
      (continuous_subtype_val.const_smul (Real.sqrt N))) (WithLp.toLp 2 J) u

private def unitRotationEquiv {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    UnitSphere N ≃ UnitSphere N where
  toFun u := ⟨U u, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using u.property⟩
  invFun u := ⟨U.symm u, by simpa only [Metric.mem_sphere, dist_zero_right,
    LinearIsometryEquiv.norm_map] using u.property⟩
  left_inv u := Subtype.ext (U.symm_apply_apply u)
  right_inv u := Subtype.ext (U.apply_symm_apply u)

private theorem harmonicSectorEnvelope_rotated {N p : ℕ} (c : ℝ) (i : Fin (p/2+1))
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : SphericalAging.FiniteModel.Disorder N p) :
    harmonicSectorEnvelope N p c i (TensorHamiltonianRotation.rotatedDisorder U J) =
      harmonicSectorEnvelope N p c i J := by
  let a := fun u : UnitSphere N => harmonicSectorFeature N p c i (physicalAxis u)
  let F := fun z : Bool × UnitSphere N => inner ℝ (signedFeature a z)
    (WithLp.toLp 2 (TensorHamiltonianRotation.rotatedDisorder U J))
  let G := fun z : Bool × UnitSphere N => inner ℝ (signedFeature a z) (WithLp.toLp 2 J)
  let e := Equiv.prodCongr (Equiv.refl Bool) (unitRotationEquiv U)
  have heval (z : Bool × UnitSphere N) : F (e z) = G z := by
    change inner ℝ (sign z.1 • a (unitRotationEquiv U z.2))
      (WithLp.toLp 2 (TensorHamiltonianRotation.rotatedDisorder U J)) =
        inner ℝ (sign z.1 • a z.2) (WithLp.toLp 2 J)
    rw [real_inner_smul_left, real_inner_smul_left]
    congr 1
    have hphys : physicalAxis (unitRotationEquiv U z.2) = U (physicalAxis z.2) := by
      change Real.sqrt N • U (z.2 : Vector N) = U (Real.sqrt N • (z.2 : Vector N))
      exact (U.map_smul _ _).symm
    change harmonicSector N p c i (TensorHamiltonianRotation.rotatedDisorder U J)
      (physicalAxis (unitRotationEquiv U z.2)) = harmonicSector N p c i J (physicalAxis z.2)
    rw [hphys, harmonicSector_rotated]
  change (⨆ z, F z) = ⨆ z, G z
  exact e.iSup_comp.symm.trans (iSup_congr heval)

abbrev SectorIndex (μ : FiniteMixture) :=
  Σ p : Degree μ.maxDegree, Fin (p.val.val/2+1)

def sectorEnvelopeConstant (μ : FiniteMixture) (p : Degree μ.maxDegree)
    (i : Fin (p.val.val/2+1)) : ℝ := by
  exact Classical.choose (zonalFeature_source_scale_upper_tail p.val.val i.val
    (by have := i.isLt; omega) (mixtureCoefficients_nonnegative μ p))

private theorem sectorEnvelopeConstant_spec (μ : FiniteMixture) (p : Degree μ.maxDegree)
    (i : Fin (p.val.val/2+1)) :
    0 < sectorEnvelopeConstant μ p i ∧ ∀ (N : ℕ), 3 ≤ N →
      (SphericalAging.FiniteModel.disorderLaw N p.val.val).real
        {J | sectorEnvelopeConstant μ p i*(N : ℝ)^(1-(i.val : ℝ)/2) <
          harmonicSectorEnvelope N p.val.val (mixtureCoefficients μ p) i J} ≤
            Real.exp (-2*(N : ℝ)) := by
  have h := Classical.choose_spec (zonalFeature_source_scale_upper_tail p.val.val i.val
    (by have := i.isLt; omega) (mixtureCoefficients_nonnegative μ p))
  refine ⟨h.1,?_⟩
  intro N hN
  apply h.2 N hN (fun u : UnitSphere N =>
    harmonicSectorFeature N p.val.val (mixtureCoefficients μ p) i (physicalAxis u))
  intro u v
  have he := harmonicSectorFeature_inner hN
    (by have hp := p.property; change 2 ≤ p.val.val at hp; omega)
    (mixtureCoefficients_nonnegative μ p) i (physicalAxis u) (physicalAxis v)
    (physicalAxis_norm_sq u) (physicalAxis_norm_sq v)
  rw [physicalAxis_overlap (by omega)] at he
  exact he

/-- Simultaneous source-scale bounds for every actual harmonic sector of
all original mixture blocks, including degree zero. -/
def harmonicSectorGood (N : ℕ) (μ : FiniteMixture) : Set (SphericalModel.Disorder N μ.maxDegree) :=
  {J | ∀ k : SectorIndex μ,
    harmonicSectorEnvelope N k.1.val.val (mixtureCoefficients μ k.1) k.2 (J k.1) ≤
      sectorEnvelopeConstant μ k.1 k.2*(N : ℝ)^(1-(k.2.val : ℝ)/2)}

private theorem harmonicSectorGood_measurable {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) :
    MeasurableSet (harmonicSectorGood N μ) := by
  unfold harmonicSectorGood
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  exact (isClosed_le ((harmonicSectorEnvelope_continuous hN k.1.val.val
    (mixtureCoefficients μ k.1) k.2).comp (by fun_prop)) continuous_const).measurableSet

private theorem harmonicSectorGood_rotated {N : ℕ} (μ : FiniteMixture)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : SphericalModel.Disorder N μ.maxDegree) :
    SphericalModel.rotatedDisorder U J ∈ harmonicSectorGood N μ ↔ J ∈ harmonicSectorGood N μ := by
  change (∀ k : SectorIndex μ,
    harmonicSectorEnvelope N k.1.val.val (mixtureCoefficients μ k.1) k.2
      (TensorHamiltonianRotation.rotatedDisorder U (J k.1)) ≤ _) ↔ _
  simp only [harmonicSectorEnvelope_rotated]
  rfl

private theorem harmonicSectorGood_failure {N : ℕ} (hN : 3 ≤ N) (μ : FiniteMixture) :
    (SphericalModel.disorderLaw N μ.maxDegree).real (harmonicSectorGood N μ)ᶜ ≤
      (Fintype.card (SectorIndex μ) : ℝ)*Real.exp (-2*(N : ℝ)) := by
  have he : (harmonicSectorGood N μ)ᶜ =
      ⋃ k : SectorIndex μ, {J : SphericalModel.Disorder N μ.maxDegree |
        sectorEnvelopeConstant μ k.1 k.2*(N : ℝ)^(1-(k.2.val : ℝ)/2) <
          harmonicSectorEnvelope N k.1.val.val (mixtureCoefficients μ k.1) k.2 (J k.1)} := by
    ext J
    simp [harmonicSectorGood, not_forall, not_le]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  calc
    _ ≤ ∑ _k : SectorIndex μ, Real.exp (-2*(N : ℝ)) := by
      apply Finset.sum_le_sum
      intro k _
      rw [(degree_block_hasLaw k.1).measureReal_eq
        (isOpen_lt continuous_const (harmonicSectorEnvelope_continuous (by omega) k.1.val.val
          (mixtureCoefficients μ k.1) k.2)).measurableSet]
      exact (sectorEnvelopeConstant_spec μ k.1 k.2).2 N hN
    _ = _ := by simp

/-- The full manuscript entrance event: the common analytic coefficient
banks together with all genuine harmonic-sector source-scale bounds. -/
def fullEntranceEvent (n : ℕ) (μ : FiniteMixture) : Set (SphericalModel.Disorder (n+1) μ.maxDegree) :=
  originalLatitudeMeanGood n μ ∩ harmonicSectorGood (n+1) μ

private theorem fullEntranceEvent_measurable {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture) :
    MeasurableSet (fullEntranceEvent n μ) :=
  (originalLatitudeMeanGood_measurable hn μ).inter (harmonicSectorGood_measurable (by omega) μ)

/-- The full coefficient event is invariant under the actual orthogonal
action on every original tensor block. -/
theorem fullEntranceEvent_rotated {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1)) (J : SphericalModel.Disorder (n+1) μ.maxDegree) :
    SphericalModel.rotatedDisorder U J ∈ fullEntranceEvent n μ ↔ J ∈ fullEntranceEvent n μ := by
  simp only [fullEntranceEvent, mem_inter_iff, originalLatitudeMeanGood_rotated hn μ,
    harmonicSectorGood_rotated μ]

/-- The full event has the exact exceptional probability printed in
`lem:ent-regularity`, with no harmonic or conditioning-mass premise. -/
theorem fullEntranceEvent_failure (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, (SphericalModel.disorderLaw (n+1) μ.maxDegree).real
      (fullEntranceEvent n μ)ᶜ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
  let A : ℝ := 1+4*(originalLatitudeBankCount μ : ℝ)+Fintype.card (SectorIndex μ)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨M,hM⟩ := exists_nat_ge (Real.log A)
  filter_upwards [eventually_ge_atTop (max M 2)] with n hn
  have he : (fullEntranceEvent n μ)ᶜ =
      (originalLatitudeMeanGood n μ)ᶜ ∪ (harmonicSectorGood (n+1) μ)ᶜ := by
    simp only [fullEntranceEvent, compl_inter]
  rw [he]
  apply (measureReal_union_le _ _).trans
  apply (add_le_add (originalLatitudeMeanGood_spare_failure (by omega) μ)
    (harmonicSectorGood_failure (by omega) μ)).trans
  calc
    _ = A*Real.exp (-2*((n+1 : ℕ) : ℝ)) := by dsimp [A]; ring
    _ = Real.exp (Real.log A-2*((n+1 : ℕ) : ℝ)) := by
      conv_lhs => arg 1; rw [← Real.exp_log hA]
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hlog : Real.log A ≤ ((n+1 : ℕ) : ℝ) :=
        hM.trans (by exact_mod_cast (show M ≤ n+1 by omega))
      linarith

/-- All three clauses of manuscript `lem:ent-regularity`, with one constant
chosen before the dimension and the actual full harmonic-sector event. -/
theorem full_entrance_regularity (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, ∃ n0 : ℕ, 0 < C ∧ ∀ n ≥ n0,
      MeasurableSet (fullEntranceEvent n μ) ∧
      (SphericalModel.disorderLaw (n+1) μ.maxDegree).real (fullEntranceEvent n μ)ᶜ ≤
        Real.exp (-((n+1 : ℕ) : ℝ)) ∧
      (∀ (U : Vector (n+1) ≃ₗᵢ[ℝ] Vector (n+1)) (J : SphericalModel.Disorder (n+1) μ.maxDegree),
        SphericalModel.rotatedDisorder U J ∈ fullEntranceEvent n μ ↔ J ∈ fullEntranceEvent n μ) ∧
      ∀ J ∈ fullEntranceEvent n μ,
        NonharmonicRegularClauses μ Q C J ∧
        ∀ (p : Degree μ.maxDegree) (i : Fin (p.val.val/2+1)) (x : Vector (n+1)),
          ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
          |harmonicSector (n+1) p.val.val (mixtureCoefficients μ p) i (J p) x| ≤
            C*((n+1 : ℕ) : ℝ)^(1-(i.val : ℝ)/2) := by
  classical
  obtain ⟨C,hC,hreg⟩ := nonharmonic_regular_event μ Q
  let D : ℝ := 1+∑ k : SectorIndex μ, sectorEnvelopeConstant μ k.1 k.2
  have hsum : 0 ≤ ∑ k : SectorIndex μ, sectorEnvelopeConstant μ k.1 k.2 :=
    Finset.sum_nonneg fun k _ => (sectorEnvelopeConstant_spec μ k.1 k.2).1.le
  have hD : 0 < D := by dsimp [D]; linarith
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp (fullEntranceEvent_failure μ)
  refine ⟨C+D,max n0 2,by positivity,?_⟩
  intro n hn
  refine ⟨fullEntranceEvent_measurable (by omega) μ,hn0 n (by omega),
    fun U J => fullEntranceEvent_rotated (by omega) μ U J,?_⟩
  intro J hJ
  obtain ⟨hm,hv,hg,hh⟩ := (hreg (n+1) (by omega)).2.2.2 J hJ.1.1
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · intro p x hx m hm3
      exact (hm p x hx m hm3).trans (mul_le_mul_of_nonneg_right
        (by linarith : C ≤ C+D) (Nat.cast_nonneg _))
    · exact hv.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+D) (Nat.cast_nonneg _))
    · exact hg.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+D) (Real.sqrt_nonneg _))
    · exact hh.trans (by linarith)
  · intro p i x hx
    have hval := harmonicSector_abs_le_envelope (by omega : 1 ≤ n+1) p.val.val
      (mixtureCoefficients μ p) i (J p) x hx
    have hgood := hJ.2 ⟨p,i⟩
    have hCi : sectorEnvelopeConstant μ p i ≤ C+D := by
      have hle : sectorEnvelopeConstant μ p i ≤
          ∑ k : SectorIndex μ, sectorEnvelopeConstant μ k.1 k.2 :=
        Finset.single_le_sum (f := fun k : SectorIndex μ => sectorEnvelopeConstant μ k.1 k.2)
          (fun k (_ : k ∈ Finset.univ) => (sectorEnvelopeConstant_spec μ k.1 k.2).1.le)
          (Finset.mem_univ (⟨p,i⟩ : SectorIndex μ))
      dsimp [D]
      linarith
    exact hval.trans (hgood.trans (mul_le_mul_of_nonneg_right hCi
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)))

def fullDisorderLaw (n : ℕ) (μ : FiniteMixture) : Measure (SphericalModel.Disorder (n+1) μ.maxDegree) :=
  ProbabilityTheory.cond (SphericalModel.disorderLaw (n+1) μ.maxDegree) (fullEntranceEvent n μ)

private theorem full_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      (1/2 : ℝ) ≤ (SphericalModel.disorderLaw (n+1) μ.maxDegree).real (fullEntranceEvent n μ) := by
  filter_upwards [fullEntranceEvent_failure μ, eventually_ge_atTop 1] with n hn hn1
  exact mass_half_of_failure _ (fullEntranceEvent_measurable hn1 μ) (by omega) hn

private theorem integral_cond_sub_event_le_twice {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E F : Set A}
    (hEF : E ⊆ F) (hhalf : (1/2 : ℝ) ≤ P.real E) (hFpos : 0 < P.real F)
    (f : A → ℝ) (hi : Integrable f P) (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂ProbabilityTheory.cond P E) ≤
      2*∫ x, f x ∂ProbabilityTheory.cond P F := by
  have hpos : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  have hinvF : 1 ≤ (P.real F)⁻¹ := (one_le_inv₀ hFpos).mpr measureReal_le_one
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_inv, ENNReal.toReal_inv]
  have hsub := setIntegral_mono_set hi.integrableOn (ae_of_all _ hf)
    (ae_of_all _ fun x hx => hEF hx)
  have hnon : 0 ≤ ∫ x in F, f x ∂P := integral_nonneg hf
  calc
    _ ≤ 2*∫ x in E, f x ∂P := mul_le_mul_of_nonneg_right hinv (integral_nonneg hf)
    _ ≤ 2*∫ x in F, f x ∂P := mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnon hinvF) (by norm_num)

private theorem unit_integrable {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {f : A → ℝ}
    (hm : Measurable f) (hf : ∀ x, f x ∈ Icc 0 1) : Integrable f P := by
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by simpa [abs_of_nonneg (hf x).1] using (hf x).2

private theorem two_exp_le {c x : ℝ} (hc : 0 < c) (hx : 2*Real.log 2/c ≤ x) :
    2*Real.exp (-c*x) ≤ Real.exp (-(c/2)*x) := by
  conv_lhs => arg 1; rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := (div_le_iff₀ hc).mp hx
  nlinarith

/-- The mixed truncated cap estimate on the full entrance coefficient event
for every smaller
positive horizon exponent. No conditioning-mass assumption remains. -/
theorem full_conditioned_mixed_truncated
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 c C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < c ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
            (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e k J ∂fullDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hall⟩ := conditioned_mixed_truncated_cap_avoidance μ hd hQ hQ1 hnp hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (full_mass_eventually μ)
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,c,C,n0,hγ0,hc,hC,hbound⟩ := hall ha haStar
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨γ0,c/2,2*C,max n0 (max n1 (max M 1)),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ hγ hγ0' e k he hk
  let f : SphericalModel.Disorder (n+1) μ.maxDegree → ℝ := sourceAxisAveragedCapHitProbability μ Q hQ hnp (2*a)
    sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e k
  have hf : ∀ J, f J ∈ Icc 0 1 := fun J => sourceAxisAveragedCapHitProbability_mem_unit ..
  have hi := unit_integrable (SphericalModel.disorderLaw (n+1) μ.maxDegree)
    (sourceAxisAveragedCapHitProbability_measurable ..) hf
  have hpos : 0 < (SphericalModel.disorderLaw (n+1) μ.maxDegree).real regularDisorder :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (regularDisorder_mass_half (by omega))
  have hcond := integral_cond_sub_event_le_twice (SphericalModel.disorderLaw (n+1) μ.maxDegree)
    (fun _ hJ => hJ.1.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
  have hr := hbound n (by omega) hγ hγ0' e k he hk
  have ht := two_exp_le hc (x := ((n+1 : ℕ) : ℝ))
    (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans (by nlinarith))

/-- Proper-pure truncated cap avoidance under that identical analytic-event
conditioning, with every amplitude and every smaller positive exponent. -/
theorem full_conditioned_pure_truncated
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 κ C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < κ ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e : ℝ, |e| ≤ B →
            (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e J ∂fullDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-κ*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
  obtain ⟨aStar,hStar,hall⟩ := conditioned_pure_truncated_cap_avoidance d hd c hc hQ hB hβ
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (full_mass_eventually μ)
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,κ,C,n0,hγ0,hκ,hC,hbound⟩ := hall ha haStar
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/κ)
  refine ⟨γ0,κ/2,2*C,max n0 (max n1 (max M 1)),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ hγ hγ0' e he
  let f : SphericalModel.Disorder (n+1) μ.maxDegree → ℝ := pureAxisAveragedCapHitProbability d (by omega) c hc Q (2*a)
    sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e
  have hf : ∀ J, f J ∈ Icc 0 1 := fun J => pureAxisAveragedCapHitProbability_mem_unit ..
  have hi := unit_integrable (SphericalModel.disorderLaw (n+1) μ.maxDegree)
    (pureAxisAveragedCapHitProbability_measurable ..) hf
  have hpos : 0 < (SphericalModel.disorderLaw (n+1) μ.maxDegree).real regularDisorder :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (regularDisorder_mass_half (by omega))
  have hcond := integral_cond_sub_event_le_twice (SphericalModel.disorderLaw (n+1) μ.maxDegree)
    (fun _ hJ => hJ.1.1) (hn1 n (by omega)) hpos f hi (fun J => (hf J).1)
  have hr := hbound n (by omega) hγ hγ0' e he
  have ht := two_exp_le hκ (x := ((n+1 : ℕ) : ℝ))
    (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans (by nlinarith))

private theorem event_cond_le_twice {A : Type*} [MeasurableSpace A]
    (P : Measure A) [IsProbabilityMeasure P] {E : Set A} (hE : MeasurableSet E)
    (hhalf : (1/2 : ℝ) ≤ P.real E) (B : Set A) :
    (ProbabilityTheory.cond P E).real B ≤ 2*P.real B := by
  rw [Measure.real, ProbabilityTheory.cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hpos : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hpos).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_right hinv ENNReal.toReal_nonneg).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_right (measure_ne_top _ _)) (by norm_num))

/-- The full entrance coefficient event lifted to the literal joint seed
space: uniform axis, original Gaussian coefficients, initial point and noise. -/
def fullBoundaryEvent (n : ℕ) (μ : FiniteMixture) :
    Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | unpackDisorder q.2.1 ∈ fullEntranceEvent n μ}

/-- Only the original disorder is conditioned. -/
def fullBoundarySeedLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (Vector (n+1) × BoundarySeed n μ) :=
  ProbabilityTheory.cond (boundarySeedLaw n μ) (fullBoundaryEvent n μ)

private theorem cond_product_left {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set A) :
    ProbabilityTheory.cond (P.prod R) (E ×ˢ univ) = (ProbabilityTheory.cond P E).prod R := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, mul_one, Measure.prod_smul_left,
    Measure.restrict_prod_eq_prod_univ]

private theorem cond_product_right {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set Z) :
    ProbabilityTheory.cond (P.prod R) (univ ×ˢ E) = P.prod (ProbabilityTheory.cond R E) := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod, measure_univ, one_mul, Measure.prod_smul_right]
  congr 1
  simpa only [Measure.restrict_univ] using (Measure.prod_restrict (μ := P) (ν := R) univ E).symm

/-- Exact independence of the uniform axis, initial point and Brownian noise
after conditioning the Gaussian disorder on the common analytic event. -/
theorem fullBoundarySeedLaw_eq_product (n : ℕ) (μ : FiniteMixture) :
    fullBoundarySeedLaw n μ =
      (sphereLaw (n+1)).prod
        ((ProbabilityTheory.cond (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
          {z | unpackDisorder z ∈ fullEntranceEvent n μ}).prod
            ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))) := by
  have he : fullBoundaryEvent n μ = univ ×ˢ
      ({z : EuclideanDisorder (n+1) μ.maxDegree |
        unpackDisorder z ∈ fullEntranceEvent n μ} ×ˢ univ) := by
    ext q
    simp only [fullBoundaryEvent, mem_ofPred_eq, mem_prod, mem_univ, true_and, and_true]
  unfold fullBoundarySeedLaw boundarySeedLaw
  rw [he, cond_product_right]
  unfold posteriorTrajectoryLaw
  rw [cond_product_left]

private theorem boundary_original_hasLaw (n : ℕ) (μ : FiniteMixture) :
    HasLaw (fun q : Vector (n+1) × BoundarySeed n μ => unpackDisorder q.2.1)
      (SphericalModel.disorderLaw (n+1) μ.maxDegree) (boundarySeedLaw n μ) := by
  have hfst : HasLaw (Prod.fst : BoundarySeed n μ → EuclideanDisorder (n+1) μ.maxDegree)
      (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) (posteriorTrajectoryLaw n μ) := by
    refine ⟨measurable_fst.aemeasurable,?_⟩
    unfold posteriorTrajectoryLaw
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hsnd : HasLaw (Prod.snd : Vector (n+1) × BoundarySeed n μ → BoundarySeed n μ)
      (posteriorTrajectoryLaw n μ) (boundarySeedLaw n μ) := by
    refine ⟨measurable_snd.aemeasurable,?_⟩
    unfold boundarySeedLaw
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hu : HasLaw (unpackDisorder (N := n+1) (P := μ.maxDegree))
      (SphericalModel.disorderLaw (n+1) μ.maxDegree) (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree)) := by
    simpa only [SYK.standardGaussianMeasureOnEuclidean, map_pi_eq_stdGaussian] using
      unpackDisorder_hasLaw (n+1) μ.maxDegree
  exact (hu.fun_comp hfst).fun_comp hsnd

private theorem boundary_full_mass_eventually (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop,
      MeasurableSet (fullBoundaryEvent n μ) ∧
      (1/2 : ℝ) ≤ (boundarySeedLaw n μ).real (fullBoundaryEvent n μ) := by
  filter_upwards [full_mass_eventually μ, eventually_ge_atTop 1] with n hn hn1
  have hm := fullEntranceEvent_measurable hn1 μ
  have he := (boundary_original_hasLaw n μ).measureReal_eq hm
  refine ⟨hm.preimage ((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_snd.fst),?_⟩
  have he' : (boundarySeedLaw n μ).real (fullBoundaryEvent n μ) =
      (SphericalModel.disorderLaw (n+1) μ.maxDegree).real (fullEntranceEvent n μ) := by
    convert he using 1 <;> congr 1
  rw [he']
  exact hn

local instance boundary_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (boundarySeedLaw n μ) := by unfold boundarySeedLaw; infer_instance

/-- Mixed original-gradient boundary control under the very same disorder
conditioning used for latitude concentration, multipliers and truncation. -/
theorem full_conditioned_mixed_boundary
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β b : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (fullBoundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ :=
    mixed_uniform_axis_gradient_cutoff_not_reached μ hnp hQ hQ1 hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_full_mass_eventually μ)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max n1 M),?_⟩
  intro n hn e k he hk
  have hr := hn0 n (by omega) e k he hk
  obtain ⟨hm,hhalf⟩ := hn1 n (by omega)
  refine ⟨hr,?_⟩
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) hm hhalf
    (mixedGradientExit n μ Q β e k b (exponentialGridHorizon γ (n+1)+2*T)
      (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans
    (two_exp_le hc (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))))

/-- Proper-pure/value boundary control on the identical analytic event. -/
theorem full_conditioned_value_boundary
    (μ : FiniteMixture) {Q B β b : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e : ℝ, |e| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (fullBoundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ := value_uniform_axis_gradient_cutoff_not_reached μ hQ hB hβ hb
  obtain ⟨n1,hn1⟩ := eventually_atTop.mp (boundary_full_mass_eventually μ)
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max n1 M),?_⟩
  intro n hn e he
  have hr := hn0 n (by omega) e he
  obtain ⟨hm,hhalf⟩ := hn1 n (by omega)
  refine ⟨hr,?_⟩
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) hm hhalf
    (valueGradientExit n μ Q β e b (exponentialGridHorizon γ (n+1)+2*T)
      (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hr (by norm_num)).trans
    (two_exp_le hc (hM.trans (by exact_mod_cast (show M ≤ n+1 by omega)))))

/-- The two concrete laws conditioned on the full entrance event have
positive normalizing mass in all sufficiently large dimensions. -/
theorem full_laws_probability (μ : FiniteMixture) :
    ∀ᶠ n : ℕ in atTop, IsProbabilityMeasure (fullDisorderLaw n μ) ∧
      IsProbabilityMeasure (fullBoundarySeedLaw n μ) := by
  filter_upwards [full_mass_eventually μ,
    boundary_full_mass_eventually μ] with n hn hb
  constructor
  · apply ProbabilityTheory.cond_isProbabilityMeasure
    intro hz
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hn
    norm_num at hn
  · apply ProbabilityTheory.cond_isProbabilityMeasure
    intro hz
    have hh := hb.2
    simp only [Measure.real, hz, ENNReal.toReal_zero] at hh
    norm_num at hh

theorem full_latitude_mean {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    (J : SphericalModel.Disorder (n+1) μ.maxDegree) (hJ : J ∈ fullEntranceEvent n μ)
    (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ))
    {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (mixtureCoefficients μ) J u (latitudeFrameAt u) r| ≤
      originalLatitudeLeadingConstant μ*Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+
        originalLatitudeCorrectionConstant μ :=
  actual_original_latitudeObservableMean_uniform_bound hn μ J hJ.1 u hu hr

/-- The literal center-field latitude mean bound on the full entrance
event, independently of the sphere logarithmic Sobolev interface. -/
theorem full_center_latitude_mean {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 ≤ Q) (J : SphericalModel.Disorder (n+1) μ.maxDegree)
    (hJ : J ∈ fullEntranceEvent n μ) (u : Vector (n+1))
    (hu : ‖u‖^2 = ((n+1 : ℕ) : ℝ)) {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 1) :
    |latitudeObservableMean (centerCoefficients (mixtureCoefficients μ) Q) J u
      (latitudeFrameAt u) r| ≤
      centerLatitudeMeanConstant μ Q*
        (Real.sqrt ((n+1 : ℕ) : ℝ)*|r|^(μ.minDegree-1)+1) :=
  actual_center_latitudeObservableMean_uniform_bound hn μ hQ J hJ.1 u hu hr

/-- The printed multiplier moments and cutoff suprema on the same
full entrance original Gaussian event, with all existing constants. -/
theorem full_mixed_multipliers (μ : FiniteMixture)
    (hd : 4 ≤ μ.minDegree) {Q M β : ℝ} (hQ : 0 < Q) (hQone : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : SphericalModel.Disorder (n+1) μ.maxDegree), J ∈ fullEntranceEvent n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^μ.minDegree ∧
        ‖gradient (fun y => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(μ.minDegree-1) := by
  obtain ⟨α₀,C,N₀,hα₀,hα₀small,hC,hbound⟩ :=
    SourceSphereSharpConcentration.mixed_source_cutoff_multipliers_and_suprema μ hd hQ hQone hnp hM hβ χ hχ hχb hχ0
  refine ⟨α₀,C,N₀,hα₀,hα₀small,hC,?_⟩
  intro n hn J hJ α hα hαsmall e k he hk x hx
  exact hbound n hn J hJ.1 α hα hαsmall e k he hk x hx

/-- The printed multiplier moments and cutoff suprema on the same
full entrance original Gaussian event, with all existing constants. -/
theorem full_pure_multipliers (p : ℕ) (hp : 4 ≤ p)
    (c : ℝ) (hc : 0 < c) {Q M β : ℝ} (hQ : 0 < Q) (hM : 0 ≤ M) (hβ : 0 ≤ β)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s, |χ s| ≤ 1) (hχ0 : ∀ s, 2 < |s| → χ s = 0) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ α₀ C : ℝ, ∃ N₀ : ℕ,
      0 < α₀ ∧ α₀ ≤ 1/8 ∧ 0 < C ∧
      ∀ (n : ℕ), N₀ ≤ n →
      ∀ (J : SphericalModel.Disorder (n+1) μ.maxDegree), J ∈ fullEntranceEvent n μ →
      ∀ α : ℝ, 0 < α → α ≤ α₀ →
      ∀ e : ℝ, |e| ≤ M →
      ∀ (x : Vector (n+1)), ‖x‖^2 = ((n+1 : ℕ) : ℝ) →
      let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-
        fieldOfMixture μ J x
      (∫ u, |Real.exp (β*W u)-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u, Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) ∧
      ∀ (u : Vector (n+1)), OnSphere u →
        |W u| ≤ C*((n+1 : ℕ) : ℝ)*α^p ∧
        ‖gradient (fun y => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ y-
            fieldOfMixture μ J y) x‖ ≤
          C*Real.sqrt ((n+1 : ℕ) : ℝ)*α^(p-1) := by
  dsimp only
  obtain ⟨α₀,C,N₀,hα₀,hα₀small,hC,hbound⟩ :=
    SourceSphereSharpConcentration.pure_source_cutoff_multipliers_and_suprema p hp c hc hQ hM hβ χ hχ hχb hχ0
  refine ⟨α₀,C,N₀,hα₀,hα₀small,hC,?_⟩
  intro n hn J hJ α hα hαsmall e he x hx
  exact hbound n hn J hJ.1 α hα hαsmall e he x hx

/-- Both clauses of `lem:ent-latitude` on the full entrance event.
The sphere logarithmic Sobolev premise is precisely the existing documented
`SourceSphereSharpConcentration.BakryEmerySphereLogSobolev` interface; no
additional harmonic, probabilistic, or concentration premise is introduced. -/
theorem full_center_latitude_mean_and_mgf (hLSI : SourceSphereSharpConcentration.BakryEmerySphereLogSobolev)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 5 ≤ n →
      ∀ (J : SphericalModel.Disorder (n+1) μ.maxDegree), J ∈ fullEntranceEvent n μ →
      ∀ (x : Vector (n+1)), ‖x‖ ^ 2 = ((n+1 : ℕ) : ℝ) →
      ∀ r ∈ Ioo (-1 : ℝ) 1,
      let c := centerCoefficients (mixtureCoefficients μ) Q
      let lat := latitudeLaw x (latitudeFrameAt x) r
      let m := ∫ u, observable c J x u ∂lat
      |m| ≤ C * (Real.sqrt ((n+1 : ℕ) : ℝ) * |r| ^ (μ.minDegree-1) + 1) ∧
      ∀ t : ℝ, mgf (fun u => observable c J x u - m) lat t ≤ Real.exp (C * t ^ 2) := by
  obtain ⟨C,hC,hbound⟩ :=
    SourceSphereSharpConcentration.center_latitude_mean_and_mgf hLSI μ hQ
  refine ⟨C,hC,?_⟩
  intro n hn J hJ x hx r hr
  exact hbound n hn J hJ.1 x hx r hr

/-- The truncated cutoff can be chosen below any prescribed positive
multiplier scale.  Taking that scale from `full_mixed_multipliers` or
`full_pure_multipliers` gives the literal order `α₁ ≤ α₀` in the manuscript. -/
theorem full_conditioned_mixed_truncated_below
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) (α0 : ℝ) (hα0 : 0 < α0) :
    ∃ aStar : ℝ, 0 < aStar ∧ 2*aStar ≤ α0 ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 c C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < c ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
            (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e k J ∂fullDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨aStar,hStar,hall⟩ := full_conditioned_mixed_truncated μ hd hQ hQ1 hnp hB hβ
  refine ⟨min aStar (α0/2),lt_min hStar (by positivity),?_,?_⟩
  · have h := min_le_right aStar (α0/2)
    linarith
  · intro a ha haStar
    exact hall ha (haStar.trans (min_le_left aStar (α0/2)))

/-- The truncated cutoff can be chosen below any prescribed positive
multiplier scale.  Taking that scale from `full_mixed_multipliers` or
`full_pure_multipliers` gives the literal order `α₁ ≤ α₀` in the manuscript. -/
theorem full_conditioned_pure_truncated_below
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) (α0 : ℝ) (hα0 : 0 < α0) :
    let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
    ∃ aStar : ℝ, 0 < aStar ∧ 2*aStar ≤ α0 ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 κ C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < κ ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e : ℝ, |e| ≤ B →
            (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β
              (exponentialGridHorizon γ (n+1)) e J ∂fullDisorderLaw n μ) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-κ*((n+1 : ℕ) : ℝ)) := by
  dsimp only
  obtain ⟨aStar,hStar,hall⟩ := full_conditioned_pure_truncated d hd c hc hQ hB hβ
  refine ⟨min aStar (α0/2),lt_min hStar (by positivity),?_,?_⟩
  · have h := min_le_right aStar (α0/2)
    linarith
  · intro a ha haStar
    exact hall ha (haStar.trans (min_le_left aStar (α0/2)))

end FullEvent

-- FULL_EVENT_END


end SlowEquilibration.SourceEntranceHarmonicSectors
