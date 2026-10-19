module

public import SlowEquilibration.BumpAveraging
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual differentials of translated bumps

These results establish the chain rule and differential bound behind
`eq:sp-bump-energy` for actual Fréchet differentials. Their specialization to
the spherical Riemannian gradient and its Dirichlet energy requires the
spherical differential/form realization; no such identification is assumed
to follow from an unrelated finite-dimensional model.
-/

namespace SlowEquilibration

open Filter MeasureTheory MeasureTheory.Measure Metric Set
open scoped Topology InnerProductSpace

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The exact chain rule for the manuscript's radial translated bump. -/
theorem hasFDerivAt_translatedBump (α : ℝ → ℝ) (N ρ : ℝ)
    (B : V → E) (D : V →L[ℝ] E) (x : V) (z : E) (d : ℝ)
    (hB : HasFDerivAt B D x)
    (hα : HasDerivAt α d (N * (1 - ‖B x - z‖ ^ 2 / ρ ^ 2))) :
    HasFDerivAt (fun y => translatedBump α N ρ (B y) z)
      ((d * (-2 * N / ρ ^ 2)) • (innerSL ℝ (B x - z)).comp D) x := by
  have harg : HasFDerivAt (fun y => N * (1 - ‖B y - z‖ ^ 2 / ρ ^ 2))
      ((-2 * N / ρ ^ 2) • (innerSL ℝ (B x - z)).comp D) x := by
    convert (((hB.sub_const z).norm_sq.const_mul (ρ ^ 2)⁻¹).const_sub 1).const_mul N using 1
    · funext y
      simp only [div_eq_mul_inv]
      ring
    · ext v
      simp only [_root_.smul_apply, _root_.neg_apply,
        ContinuousLinearMap.comp_apply, smul_eq_mul]
      ring
  simpa only [Function.comp_def, translatedBump, smul_smul] using
    hα.comp_hasFDerivAt x harg

/-- A differentiable cutoff constant on the negative half-line has derivative
zero at every strictly negative point. -/
theorem cutoff_derivative_zero_of_negative (α : ℝ → ℝ) (t d : ℝ)
    (hαzero : ∀ s ≤ 0, α s = 0) (ht : t < 0) (hα : HasDerivAt α d t) : d = 0 := by
  have heq : α =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) :=
    (eventually_lt_nhds ht).mono (fun s hs => hαzero s hs.le)
  exact hα.unique ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq heq)

/-- Norm estimate for the actual bump differential before restricting its
support. -/
theorem translatedBump_differential_norm_bound (N ρ d : ℝ)
    (D : V →L[ℝ] E) (b z : E) (hN : 0 ≤ N) (hρ : 0 < ρ) :
    ‖(d * (-2 * N / ρ ^ 2)) • (innerSL ℝ (b - z)).comp D‖ ≤
      (2 * N / ρ ^ 2) * |d| * ‖b - z‖ * ‖D‖ := by
  have hscale : |d * (-2 * N / ρ ^ 2)| = (2 * N / ρ ^ 2) * |d| := by
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg hN,
      abs_of_nonneg (sq_nonneg ρ)]
    norm_num
    ring
  rw [norm_smul, Real.norm_eq_abs, hscale]
  calc
    _ ≤ ((2 * N / ρ ^ 2) * |d|) * (‖innerSL ℝ (b - z)‖ * ‖D‖) :=
      mul_le_mul_of_nonneg_left ((innerSL ℝ (b - z)).opNorm_comp_le D) (by positivity)
    _ = _ := by rw [innerSL_apply_norm]; ring

/-- The actual squared differential of a radial bump is bounded on its
support by the observable differential. The derivative of the cutoff is
bounded by `K`. -/
theorem translatedBump_differential_sq_bound_inside (N ρ d K : ℝ)
    (D : V →L[ℝ] E) (b z : E) (hN : 0 ≤ N) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hd : |d| ≤ K) (hclose : ‖b - z‖ ≤ ρ) :
    ‖(d * (-2 * N / ρ ^ 2)) • (innerSL ℝ (b - z)).comp D‖ ^ 2 ≤
      (4 * K ^ 2 * N ^ 2 / ρ ^ 2) * ‖D‖ ^ 2 := by
  have hnorm := translatedBump_differential_norm_bound N ρ d D b z hN hρ
  have hfirst : (2 * N / ρ ^ 2) * |d| * ‖b - z‖ * ‖D‖ ≤
      (2 * N * K / ρ) * ‖D‖ := by
    calc
      _ ≤ (2 * N / ρ ^ 2) * K * ρ * ‖D‖ := by gcongr
      _ = _ := by field_simp [ne_of_gt hρ]
  have hlower : 0 ≤ (2 * N * K / ρ) * ‖D‖ := by positivity
  have hsquare : ‖(d * (-2 * N / ρ ^ 2)) • (innerSL ℝ (b - z)).comp D‖ ^ 2 ≤
      ((2 * N * K / ρ) * ‖D‖) ^ 2 := by
    nlinarith [norm_nonneg ((d * (-2 * N / ρ ^ 2)) • (innerSL ℝ (b - z)).comp D)]
  calc
    _ ≤ _ := hsquare
    _ = _ := by field_simp [ne_of_gt hρ]; ring

/-- The derivative bound has the same compact parameter support as the bump.
Outside the support, zero derivative is proved from the cutoff's constant
negative half-line rather than supplied as a hypothesis. -/
theorem translatedBump_fderiv_sq_support_bound (α : ℝ → ℝ) (N ρ K : ℝ)
    (B : V → E) (D : V →L[ℝ] E) (x : V) (z : E)
    (hB : HasFDerivAt B D x) (hα : Differentiable ℝ α)
    (hN : 0 < N) (hρ : 0 < ρ) (hK : 0 ≤ K)
    (hαbound : ∀ t, |deriv α t| ≤ K) (hαzero : ∀ t ≤ 0, α t = 0) :
    ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2 ≤
      ((4 * K ^ 2 * N ^ 2 / ρ ^ 2) * ‖D‖ ^ 2) *
        (closedBall (B x) ρ).indicator (fun _ => (1 : ℝ)) z := by
  let t := N * (1 - ‖B x - z‖ ^ 2 / ρ ^ 2)
  have hαt : HasDerivAt α (deriv α t) t := (hα t).hasDerivAt
  have hchain := hasFDerivAt_translatedBump α N ρ B D x z (deriv α t) hB hαt
  rw [hchain.fderiv]
  by_cases hz : z ∈ closedBall (B x) ρ
  · have hclose : ‖B x - z‖ ≤ ρ := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
    simpa [hz] using translatedBump_differential_sq_bound_inside N ρ (deriv α t) K
      D (B x) z hN.le hρ hK (hαbound t) hclose
  · have hfar : ρ < ‖B x - z‖ := by
      simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev, not_le] using hz
    have hsquare : ρ ^ 2 < ‖B x - z‖ ^ 2 := by nlinarith [norm_nonneg (B x - z)]
    have hratio : 1 < ‖B x - z‖ ^ 2 / ρ ^ 2 := (one_lt_div (sq_pos_of_pos hρ)).2 hsquare
    have ht : t < 0 := by dsimp [t]; nlinarith
    have hd : deriv α t = 0 := cutoff_derivative_zero_of_negative α t (deriv α t) hαzero ht hαt
    simp [hz, hd]

/-- The continuum parameter integral of the actual squared bump differential
is bounded by `4*K²*N²/ρ²` times the squared observable differential norm.
The integrability of this differential is derived from its genuine continuous
formula and compact parameter support. -/
theorem averaged_translatedBump_fderiv_sq_bound
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsAddHaarMeasure ν] (α : ℝ → ℝ) (N ρ K : ℝ)
    (B : V → E) (D : V →L[ℝ] E) (x : V)
    (hB : HasFDerivAt B D x) (hα : Differentiable ℝ α) (hαderiv : Continuous (deriv α))
    (hN : 0 < N) (hρ : 0 < ρ) (hK : 0 ≤ K) (hBnorm : ‖B x‖ ≤ 1)
    (hαbound : ∀ t, |deriv α t| ≤ K) (hαzero : ∀ t ≤ 0, α t = 0) :
    Integrable (fun z => ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2)
      (bumpIndexMeasure ν ρ) ∧
      (∫ z, ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2
        ∂bumpIndexMeasure ν ρ) ≤ (4 * K ^ 2 * N ^ 2 / ρ ^ 2) * ‖D‖ ^ 2 := by
  let μ := bumpIndexMeasure ν ρ
  let : IsFiniteMeasure μ := bumpIndexMeasure_isFinite ν ρ hρ
  let A : ℝ := (4 * K ^ 2 * N ^ 2 / ρ ^ 2) * ‖D‖ ^ 2
  have heq : (fun z => fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x) =
      (fun z => ((deriv α (N * (1 - ‖B x - z‖ ^ 2 / ρ ^ 2))) * (-2 * N / ρ ^ 2)) •
        (innerSL ℝ (B x - z)).comp D) := by
    funext z
    exact (hasFDerivAt_translatedBump α N ρ B D x z _ hB
      ((hα _).hasDerivAt)).fderiv
  have hmapCont : Continuous (fun z => fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x) := by
    rw [heq]
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun z => ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2) μ :=
    (hmapCont.norm.pow 2).aestronglyMeasurable
  have hbound : ∀ z, ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2 ≤
      A * (closedBall (B x) ρ).indicator (fun _ => (1 : ℝ)) z :=
    fun z => translatedBump_fderiv_sq_support_bound α N ρ K B D x z hB hα hN hρ hK hαbound hαzero
  have hdomInt : Integrable (fun z => A * (closedBall (B x) ρ).indicator (fun _ => (1 : ℝ)) z) μ :=
    ((integrable_const (1 : ℝ)).indicator measurableSet_closedBall).const_mul A
  have hgInt := hdomInt.mono_nonneg hmeas (Eventually.of_forall (fun _ => sq_nonneg _))
    (Eventually.of_forall hbound)
  refine ⟨hgInt, ?_⟩
  calc
    _ ≤ ∫ z, A * (closedBall (B x) ρ).indicator (fun _ => (1 : ℝ)) z ∂μ :=
      integral_mono_ae hgInt hdomInt (Eventually.of_forall hbound)
    _ = A * μ.real (closedBall (B x) ρ) := by
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) measurableSet_closedBall]
      simp
    _ = A := by simp [μ, measureReal_def, bumpIndexMeasure_supportBall ν ρ (B x) hρ hBnorm]

/-- The actual vector differential's squared operator norm is bounded by the
sum of the squared coordinate differential norms in any genuine orthonormal
basis. This is the comparison with the squared Hilbert--Schmidt gradient
appearing in the manuscript's vector Dirichlet energy. -/
theorem differential_norm_sq_le_coordinate_sum {ι : Type*} [Fintype ι]
    (basis : OrthonormalBasis ι ℝ E) (D : V →L[ℝ] E) :
    ‖D‖ ^ 2 ≤ ∑ i, ‖(innerSL ℝ (basis i)).comp D‖ ^ 2 := by
  let S : ℝ := ∑ i, ‖(innerSL ℝ (basis i)).comp D‖ ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hpoint : ∀ v, ‖D v‖ ^ 2 ≤ S * ‖v‖ ^ 2 := by
    intro v
    calc
      _ = ∑ i, ‖inner ℝ (basis i) (D v)‖ ^ 2 := (basis.sum_sq_norm_inner_right (D v)).symm
      _ ≤ ∑ i, ‖(innerSL ℝ (basis i)).comp D‖ ^ 2 * ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        have hbound := ((innerSL ℝ (basis i)).comp D).le_opNorm v
        have hnorm : 0 ≤ ‖(innerSL ℝ (basis i)).comp D‖ * ‖v‖ := by positivity
        simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, mul_pow] using
          (show ‖((innerSL ℝ (basis i)).comp D) v‖ ^ 2 ≤
            (‖(innerSL ℝ (basis i)).comp D‖ * ‖v‖) ^ 2 by
              nlinarith [norm_nonneg (((innerSL ℝ (basis i)).comp D) v)])
      _ = _ := by rw [← Finset.sum_mul]
  have hop : ‖D‖ ≤ Real.sqrt S := by
    apply D.opNorm_le_bound (Real.sqrt_nonneg S)
    intro v
    have hsq : (Real.sqrt S * ‖v‖) ^ 2 = S * ‖v‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hS]
    nlinarith [hpoint v, norm_nonneg (D v), mul_nonneg (Real.sqrt_nonneg S) (norm_nonneg v)]
  nlinarith [Real.sq_sqrt hS, norm_nonneg D, Real.sqrt_nonneg S]

/-- The continuum differential estimate in the manuscript's coordinate
gradient-square normalization. All derivatives, parameter integrals, and the
orthonormal output basis are actual objects. -/
theorem averaged_translatedBump_fderiv_sq_coordinate_bound
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ E)
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (ν : Measure E) [IsAddHaarMeasure ν] (α : ℝ → ℝ) (N ρ K : ℝ)
    (B : V → E) (D : V →L[ℝ] E) (x : V)
    (hB : HasFDerivAt B D x) (hα : Differentiable ℝ α) (hαderiv : Continuous (deriv α))
    (hN : 0 < N) (hρ : 0 < ρ) (hK : 0 ≤ K) (hBnorm : ‖B x‖ ≤ 1)
    (hαbound : ∀ t, |deriv α t| ≤ K) (hαzero : ∀ t ≤ 0, α t = 0) :
    (∫ z, ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2
      ∂bumpIndexMeasure ν ρ) ≤
      (4 * K ^ 2 * N ^ 2 / ρ ^ 2) * ∑ i, ‖(innerSL ℝ (basis i)).comp D‖ ^ 2 := by
  have haverage := averaged_translatedBump_fderiv_sq_bound ν α N ρ K B D x
    hB hα hαderiv hN hρ hK hBnorm hαbound hαzero
  exact haverage.2.trans (mul_le_mul_of_nonneg_left
    (differential_norm_sq_le_coordinate_sum basis D) (by positivity))

/-- The whole-state energy averaging argument for genuine differentiable
maps on a finite-dimensional real normed domain and an arbitrary finite
state measure. The explicit bump's actual Fréchet differential is used on
the left; the right is the integral of its actual orthonormal coordinate
derivative squares. Product integrability and Fubini are proved from the
compact parameter support and the finite coordinate energy.

This provides the complete measure integration step behind
`eq:sp-bump-energy`. Its use for the spherical intrinsic gradient requires
the separate manifold differential/Dirichlet-form identification. -/
theorem averaged_translatedBump_differential_energy_bound
    {ι : Type*} [Fintype ι] (basis : OrthonormalBasis ι ℝ E)
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (ν : Measure E) [IsAddHaarMeasure ν] (π : Measure V) [IsFiniteMeasure π]
    (α : ℝ → ℝ) (N ρ K : ℝ) (B : V → E) (D : V → V →L[ℝ] E)
    (hB : ∀ x, HasFDerivAt B (D x) x) (hD : Continuous D)
    (hα : Differentiable ℝ α) (hαderiv : Continuous (deriv α))
    (hN : 0 < N) (hρ : 0 < ρ) (hK : 0 ≤ K) (hBnorm : ∀ᵐ x ∂π, ‖B x‖ ≤ 1)
    (hαbound : ∀ t, |deriv α t| ≤ K) (hαzero : ∀ t ≤ 0, α t = 0)
    (henergy : Integrable (fun x => ∑ i, ‖(innerSL ℝ (basis i)).comp (D x)‖ ^ 2) π) :
    Integrable (fun z => ∫ x, ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2 ∂π)
      (bumpIndexMeasure ν ρ) ∧
      (∫ z, ∫ x, ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) z) x‖ ^ 2 ∂π
        ∂bumpIndexMeasure ν ρ) ≤
      (4 * K ^ 2 * N ^ 2 / ρ ^ 2) *
        (∫ x, ∑ i, ‖(innerSL ℝ (basis i)).comp (D x)‖ ^ 2 ∂π) := by
  let μ := bumpIndexMeasure ν ρ
  let : IsFiniteMeasure μ := bumpIndexMeasure_isFinite ν ρ hρ
  let A : ℝ := 4 * K ^ 2 * N ^ 2 / ρ ^ 2
  let H : V → ℝ := fun x => ∑ i, ‖(innerSL ℝ (basis i)).comp (D x)‖ ^ 2
  let g : E × V → ℝ := fun p => ‖fderiv ℝ (fun y => translatedBump α N ρ (B y) p.1) p.2‖ ^ 2
  have hBcont : Continuous B := (show Differentiable ℝ B from fun x => (hB x).differentiableAt).continuous
  have heq : g = (fun p =>
      ‖((deriv α (N * (1 - ‖B p.2 - p.1‖ ^ 2 / ρ ^ 2))) * (-2 * N / ρ ^ 2)) •
        (innerSL ℝ (B p.2 - p.1)).comp (D p.2)‖ ^ 2) := by
    funext p
    dsimp [g]
    rw [(hasFDerivAt_translatedBump α N ρ B (D p.2) p.2 p.1 _ (hB p.2)
      ((hα _).hasDerivAt)).fderiv]
  have hgcont : Continuous g := by rw [heq]; fun_prop
  have hgnonneg : ∀ p, 0 ≤ g p := fun _ => sq_nonneg _
  have havg : ∀ᵐ x ∂π, Integrable (fun z => g (z, x)) μ ∧
      (∫ z, g (z, x) ∂μ) ≤ A * H x := by
    filter_upwards [hBnorm] with x hx
    refine ⟨(averaged_translatedBump_fderiv_sq_bound ν α N ρ K B (D x) x
      (hB x) hα hαderiv hN hρ hK hx hαbound hαzero).1, ?_⟩
    exact averaged_translatedBump_fderiv_sq_coordinate_bound basis ν α N ρ K B (D x) x
      (hB x) hα hαderiv hN hρ hK hx hαbound hαzero
  have hOuterMeas : AEStronglyMeasurable (fun x => ∫ z, ‖g (z, x)‖ ∂μ) π :=
    hgcont.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  have hOuterInt : Integrable (fun x => ∫ z, ‖g (z, x)‖ ∂μ) π := by
    apply (henergy.const_mul A).mono_nonneg hOuterMeas
      (Eventually.of_forall (fun x => integral_nonneg (fun z => norm_nonneg _)))
    filter_upwards [havg] with x hx
    simpa only [Real.norm_of_nonneg (hgnonneg _)] using hx.2
  have hgInt : Integrable g (μ.prod π) :=
    (integrable_prod_iff' hgcont.aestronglyMeasurable).2
      ⟨havg.mono (fun _ h => h.1), hOuterInt⟩
  refine ⟨hgInt.integral_prod_left, ?_⟩
  calc
    _ = ∫ x, ∫ z, g (z, x) ∂μ ∂π := integral_integral_swap hgInt
    _ ≤ ∫ x, A * H x ∂π := integral_mono_ae hgInt.integral_prod_right
      (henergy.const_mul A) (havg.mono (fun _ h => h.2))
    _ = _ := integral_const_mul _ _

end SlowEquilibration
