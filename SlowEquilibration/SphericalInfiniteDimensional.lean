module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalClosability
public import SlowEquilibration.SphereVolume
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.MeasureTheory.Measure.OpenPos

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

open MeasureTheory Filter Set Polynomial
open SphericalModel
open SphericalAging.HardSphereDynamics
open scoped BigOperators InnerProductSpace Topology

/-- The actual Gibbs law has precisely the same null sets as the actual
uniform spherical law. Positivity is proved from the actual density. -/
theorem sphereLaw_absolutelyContinuous_gibbsLaw {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) : sphereLaw N ≪ gibbsLaw N β H :=
  withDensity_absolutelyContinuous'
    ((gibbsDensity_continuous β hH).measurable.ennreal_ofReal.aemeasurable)
    (ae_of_all _ (fun x => (ENNReal.ofReal_pos.mpr (gibbsDensity_pos hN β hH x)).ne'))

/-- A continuous ambient observable that vanishes almost everywhere under
actual Gibbs measure vanishes at every point of the actual sphere. -/
theorem continuous_eq_zero_onSphere_of_gibbs_ae {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f : Vector N → ℝ} (hH : Continuous H) (hf : Continuous f)
    (hae : f =ᵐ[gibbsLaw N β H] 0) (x : Vector N) (hx : OnSphere x) : f x = 0 := by
  let : NeZero N := ⟨by omega⟩
  have hν : f =ᵐ[sphereLaw N] 0 :=
    hae.filter_mono (sphereLaw_absolutelyContinuous_gibbsLaw hN β hH).ae_le
  change f =ᵐ[SphericalAging.SphereInitialLaw.sphereLaw N] 0 at hν
  rw [SphereVolume.sphereLaw_eq_normalized_angular N hN] at hν
  have hθ := ae_of_ae_map (by fun_prop : AEMeasurable
    (fun u : Metric.sphere (0 : Vector N) 1 => Real.sqrt (N : ℝ) • (u : Vector N))
    (SphereVolume.unitAngular (Vector N))) hν
  let : (SphereVolume.unitAngular (Vector N)).IsOpenPosMeasure :=
    Measure.isOpenPosMeasure_smul (μ := (volume : Measure (Vector N)).toSphere)
      (ENNReal.inv_ne_zero.mpr (measure_ne_top _ _))
  have heq : (fun u : Metric.sphere (0 : Vector N) 1 => f (Real.sqrt (N : ℝ) • (u : Vector N))) =
      (fun _ => (0 : ℝ)) := Measure.eq_of_ae_eq hθ
    (hf.comp (continuous_subtype_val.const_smul (Real.sqrt (N : ℝ)))) continuous_const
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hxn : ‖x‖ = Real.sqrt (N : ℝ) :=
    SphericalAging.LandscapeDerivatives.sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  let u : Metric.sphere (0 : Vector N) 1 := ⟨(Real.sqrt (N : ℝ))⁻¹ • x, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hs), hxn, inv_mul_cancel₀ hs.ne']⟩
  have hux : Real.sqrt (N : ℝ) • (u : Vector N) = x := by
    dsimp [u]
    rw [smul_smul, mul_inv_cancel₀ hs.ne', one_smul]
  have he := congrFun heq u
  rwa [hux] at he

/-- A genuine spin coordinate whose values fill a nontrivial real interval. -/
def spinHeight {N : ℕ} (hN : 2 ≤ N) (x : Vector N) : ℝ :=
  x ⟨0, by omega⟩ / Real.sqrt (N : ℝ)

theorem spinHeight_continuous {N : ℕ} (hN : 2 ≤ N) : Continuous (spinHeight hN) :=
  (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) ⟨0, by omega⟩).div_const _

/-- The actual radius-√N sphere realizes every height in `(-1,1)` when
`N≥2`, by an explicit two-coordinate spherical vector. -/
theorem spinHeight_surjective_interval {N : ℕ} (hN : 2 ≤ N) (r : ℝ)
    (hr : r ∈ Ioo (-1 : ℝ) 1) : ∃ x : Vector N, OnSphere x ∧ spinHeight hN x = r := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have hv := congrArg Fin.val he; norm_num [i, j] at hv
  have hji : j ≠ i := hij.symm
  have hpos : 0 < 1 - r ^ 2 := by nlinarith [mul_pos (show 0 < r + 1 by linarith [hr.1]) (show 0 < 1 - r by linarith [hr.2])]
  let u : Vector N := r • basisVector i + Real.sqrt (1 - r ^ 2) • basisVector j
  have huu : inner ℝ u u = 1 := by
    dsimp [u]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      basisVector, EuclideanSpace.inner_single_left, PiLp.single_apply, conj_trivial,
      hij, hji, ite_true, ite_false, mul_zero, add_zero, zero_add, mul_one]
    nlinarith [Real.sq_sqrt hpos.le]
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  refine ⟨Real.sqrt (N : ℝ) • u, ?_, ?_⟩
  · change inner ℝ (Real.sqrt (N : ℝ) • u) (Real.sqrt (N : ℝ) • u) = (N : ℝ)
    rw [real_inner_smul_left, real_inner_smul_right, huu, mul_one, ← pow_two,
      Real.sq_sqrt (Nat.cast_nonneg N)]
  · unfold spinHeight
    dsimp [u]
    simp only [basisVector, PiLp.single_apply]
    have h0i : (⟨0, by omega⟩ : Fin N) = i := rfl
    simp only [h0i, hij, ite_true, ite_false, mul_one, mul_zero, add_zero]
    exact mul_div_cancel_left₀ r hs.ne'

/-- Polynomial functions of the actual spin coordinate, in the actual Gibbs
L² space. This map will be proved injective from the actual sphere support. -/
def polynomialSpinL2 {N : ℕ} (hN : 2 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) : ℝ[X] →ₗ[ℝ] Lp ℝ 2 (gibbsLaw N β H) where
  toFun p := gibbsToL2 (by omega) β H hH (fun x => p.eval (spinHeight hN x))
    (p.continuous.comp (spinHeight_continuous hN))
  map_add' p q := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe (by omega) β H hH (fun x => (p + q).eval (spinHeight hN x))
      ((p + q).continuous.comp (spinHeight_continuous hN)),
      Lp.coeFn_add
        (gibbsToL2 (by omega) β H hH (fun x => p.eval (spinHeight hN x)) (p.continuous.comp (spinHeight_continuous hN)))
        (gibbsToL2 (by omega) β H hH (fun x => q.eval (spinHeight hN x)) (q.continuous.comp (spinHeight_continuous hN))),
      gibbsToL2_coe (by omega) β H hH (fun x => p.eval (spinHeight hN x)) (p.continuous.comp (spinHeight_continuous hN)),
      gibbsToL2_coe (by omega) β H hH (fun x => q.eval (spinHeight hN x)) (q.continuous.comp (spinHeight_continuous hN))] with x hx hsum hp hq
    simpa only [hx, hsum, hp, hq, Pi.add_apply] using Polynomial.eval_add
  map_smul' c p := by
    apply Lp.ext
    filter_upwards [gibbsToL2_coe (by omega) β H hH (fun x => (c • p).eval (spinHeight hN x))
      ((c • p).continuous.comp (spinHeight_continuous hN)),
      Lp.coeFn_smul c
        (gibbsToL2 (by omega) β H hH (fun x => p.eval (spinHeight hN x)) (p.continuous.comp (spinHeight_continuous hN))),
      gibbsToL2_coe (by omega) β H hH (fun x => p.eval (spinHeight hN x)) (p.continuous.comp (spinHeight_continuous hN))] with x hx hsmul hp
    simpa only [hx, hsmul, hp, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      (Polynomial.eval_smul c p (spinHeight hN x))

/-- The actual spin polynomial map is injective. An a.e. equality is promoted
to pointwise sphere equality using the constructed angular law, and the
actual interval of heights forces a polynomial to vanish identically. -/
theorem polynomialSpinL2_injective {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : Function.Injective (polynomialSpinL2 hN β H hH) := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro p hp
  have hzero : polynomialSpinL2 hN β H hH p = 0 := hp
  have hae : (fun x => p.eval (spinHeight hN x)) =ᵐ[gibbsLaw N β H] 0 :=
    (gibbsToL2_coe (by omega) β H hH _ (p.continuous.comp (spinHeight_continuous hN))).symm.trans
      (Lp.eq_zero_iff_ae_eq_zero.mp hzero)
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply (Set.Ioo_infinite (show (-1 : ℝ) < 1 by norm_num)).mono
  intro r hr
  obtain ⟨x, hx, hheight⟩ := spinHeight_surjective_interval hN r hr
  have h := continuous_eq_zero_onSphere_of_gibbs_ae (by omega) β hH
    (p.continuous.comp (spinHeight_continuous hN)) hae x hx
  change p.eval r = 0
  simpa only [Polynomial.IsRoot, Function.comp_def, hheight] using h

/-- The manuscript's actual spherical Gibbs L² space is infinite-dimensional
in every dimension at least two and for every continuous realized field. -/
theorem sphericalL2_not_finiteDimensional {N : ℕ} (hN : 2 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) : ¬ FiniteDimensional ℝ (Lp ℝ 2 (gibbsLaw N β H)) := by
  intro hfinite
  let := hfinite
  have hpoly : FiniteDimensional ℝ ℝ[X] :=
    FiniteDimensional.of_injective (polynomialSpinL2 hN β H hH) (polynomialSpinL2_injective hN β H hH)
  exact Polynomial.not_finite hpoly

end
end SlowEquilibration.SphericalForm
