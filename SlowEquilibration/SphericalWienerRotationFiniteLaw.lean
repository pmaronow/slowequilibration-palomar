-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWienerRotation
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-! Finite-dimensional laws of the actual product Wiener driver under
orthogonal rotations. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalWienerRotationFiniteLaw

open SphericalModel SphericalAging MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalWienerRotation
open scoped Topology NNReal ENNReal
set_option autoImplicit false

theorem wiener_raw_vector_time_law {N : ℕ} (t : ℝ≥0) :
    (VectorBrownian.law N).map
        (fun ω : VectorBrownian.Space N => fun i : Fin N => ω i t) =
      Measure.pi (fun _ : Fin N => gaussianReal 0 t) := by
  rw [VectorBrownian.law, Measure.pi_map_pi
    (fun _ : Fin N => (VectorBrownian.scalar_eval_measurable t).aemeasurable)]
  congr 1
  funext i
  exact VectorBrownian.scalar_isPreBrownian.hasLaw_eval t |>.map_eq

theorem gaussianReal_time_eq_scaled_standard (t : ℝ≥0) :
    gaussianReal 0 t =
      (gaussianReal 0 1).map (fun z : ℝ => Real.sqrt (t : ℝ)*z) := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · ext
    simp [Real.sq_sqrt t.coe_nonneg]

theorem wienerVector_time_law {N : ℕ} (t : ℝ≥0) :
    (VectorBrownian.law N).map (wienerVector t) =
      (stdGaussian (Vector N)).map (fun z => Real.sqrt (t : ℝ) • z) := by
  let c : ℝ := Real.sqrt (t : ℝ)
  let raw : VectorBrownian.Space N → (Fin N → ℝ) :=
    fun ω i => ω i t
  have hraw : Measurable raw := measurable_pi_iff.mpr
    (fun i => VectorBrownian.coordinate_measurable i t)
  have hscalar : ∀ i : Fin N,
      gaussianReal 0 t = (gaussianReal 0 1).map (fun z : ℝ => c*z) := by
    intro i
    exact gaussianReal_time_eq_scaled_standard t
  have hmap :
      (Measure.pi (fun _ : Fin N => gaussianReal 0 t)).map (WithLp.toLp 2) =
        (stdGaussian (Vector N)).map (fun z => c • z) := by
    rw [show (fun _ : Fin N => gaussianReal 0 t) =
      (fun _ : Fin N => (gaussianReal 0 1).map (fun z : ℝ => c*z)) by
        funext i; exact hscalar i]
    rw [← Measure.pi_map_pi (fun _ : Fin N =>
      (show Measurable (fun z : ℝ => c*z) by fun_prop).aemeasurable)]
    rw [Measure.map_map (PiLp.continuous_toLp 2 _).measurable
      (measurable_pi_iff.mpr (fun _ => by fun_prop))]
    have hfun :
        (fun f : Fin N → ℝ => WithLp.toLp 2 (fun i => c*f i)) =
          (fun z : Vector N => c • z) ∘ (WithLp.toLp 2) := by
      funext f
      ext i
      rfl
    change (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
      (fun f : Fin N → ℝ => WithLp.toLp 2 (fun i => c*f i)) = _
    rw [hfun, ← Measure.map_map (by fun_prop : Measurable (fun z : Vector N => c • z))
      (PiLp.continuous_toLp 2 _).measurable]
    rw [map_pi_eq_stdGaussian]
  change (VectorBrownian.law N).map ((WithLp.toLp 2) ∘ raw) = _
  rw [← Measure.map_map (PiLp.continuous_toLp 2 _).measurable hraw,
    wiener_raw_vector_time_law t]
  exact hmap

theorem wienerVector_time_rotation_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (t : ℝ≥0) :
    (VectorBrownian.law N).map (fun ω => U (wienerVector t ω)) =
      (VectorBrownian.law N).map (wienerVector t) := by
  change (VectorBrownian.law N).map (U ∘ wienerVector t) = _
  rw [← Measure.map_map U.continuous.measurable (wienerVector_measurable t),
    wienerVector_time_law]
  let c : ℝ := Real.sqrt (t : ℝ)
  have hfun : U ∘ (fun z : Vector N => c • z) =
      (fun z : Vector N => c • z) ∘ U := by
    funext z
    exact U.map_smul c z
  rw [Measure.map_map U.continuous.measurable (by fun_prop : Measurable (fun z : Vector N => c • z)),
    hfun, ← Measure.map_map (by fun_prop : Measurable (fun z : Vector N => c • z)) U.continuous.measurable,
    stdGaussian_map U]

theorem wiener_raw_vector_increment_law {N : ℕ}
    (s t : ℝ≥0) (hst : s ≤ t) :
    (VectorBrownian.law N).map
        (fun ω : VectorBrownian.Space N => fun i : Fin N => ω i t - ω i s) =
      Measure.pi (fun _ : Fin N => gaussianReal 0 (t-s)) := by
  have hv : nndist (t : ℝ) (s : ℝ) = t-s := by
    ext
    simp only [coe_nndist,Real.dist_eq,abs_of_nonneg
      (sub_nonneg.mpr (show (s : ℝ) ≤ t from hst)),NNReal.coe_sub hst]
  rw [VectorBrownian.law]
  change (Measure.pi (fun _ : Fin N => VectorBrownian.pathLaw)).map
    (fun ω i => (fun η : VectorBrownian.Path => η t - η s) (ω i)) = _
  have hpi := Measure.pi_map_pi
    (μ := fun _ : Fin N => VectorBrownian.pathLaw)
    (f := fun _ (η : VectorBrownian.Path) => η t - η s)
    (fun _ : Fin N => ((VectorBrownian.scalar_eval_measurable t).sub
      (VectorBrownian.scalar_eval_measurable s)).aemeasurable)
  rw [hpi]
  congr 1
  funext i
  rw [← hv]
  exact VectorBrownian.scalar_isPreBrownian.hasLaw_sub t s |>.map_eq

theorem wienerVector_increment_law {N : ℕ}
    (s t : ℝ≥0) (hst : s ≤ t) :
    (VectorBrownian.law N).map (fun ω => wienerVector t ω - wienerVector s ω) =
      (stdGaussian (Vector N)).map (fun z => Real.sqrt ((t-s : ℝ≥0) : ℝ) • z) := by
  let v : ℝ≥0 := t-s
  let c : ℝ := Real.sqrt (v : ℝ)
  let raw : VectorBrownian.Space N → (Fin N → ℝ) :=
    fun ω i => ω i t - ω i s
  have hraw : Measurable raw := measurable_pi_iff.mpr
    (fun i => (VectorBrownian.coordinate_measurable i t).sub
      (VectorBrownian.coordinate_measurable i s))
  have hscalar : ∀ i : Fin N,
      gaussianReal 0 v = (gaussianReal 0 1).map (fun z : ℝ => c*z) := by
    intro i
    exact gaussianReal_time_eq_scaled_standard v
  have hmap :
      (Measure.pi (fun _ : Fin N => gaussianReal 0 v)).map (WithLp.toLp 2) =
        (stdGaussian (Vector N)).map (fun z => c • z) := by
    rw [show (fun _ : Fin N => gaussianReal 0 v) =
      (fun _ : Fin N => (gaussianReal 0 1).map (fun z : ℝ => c*z)) by
        funext i; exact hscalar i]
    rw [← Measure.pi_map_pi (fun _ : Fin N =>
      (show Measurable (fun z : ℝ => c*z) by fun_prop).aemeasurable)]
    rw [Measure.map_map (PiLp.continuous_toLp 2 _).measurable
      (measurable_pi_iff.mpr (fun _ => by fun_prop))]
    change (Measure.pi (fun _ : Fin N => gaussianReal 0 1)).map
      (fun f : Fin N → ℝ => WithLp.toLp 2 (fun i => c*f i)) = _
    have hfun :
        (fun f : Fin N → ℝ => WithLp.toLp 2 (fun i => c*f i)) =
          (fun z : Vector N => c • z) ∘ (WithLp.toLp 2) := by
      funext f
      ext i
      rfl
    rw [hfun, ← Measure.map_map (by fun_prop : Measurable (fun z : Vector N => c • z))
      (PiLp.continuous_toLp 2 _).measurable]
    rw [map_pi_eq_stdGaussian]
  have heq : (fun ω : VectorBrownian.Space N =>
      wienerVector t ω - wienerVector s ω) =
      (WithLp.toLp 2) ∘ raw := by
    funext ω
    ext i
    rfl
  rw [heq, ← Measure.map_map (PiLp.continuous_toLp 2 _).measurable hraw,
    wiener_raw_vector_increment_law s t hst]
  exact hmap

theorem wienerVector_increment_rotation_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (s t : ℝ≥0) (hst : s ≤ t) :
    (VectorBrownian.law N).map
        (fun ω => U (wienerVector t ω - wienerVector s ω)) =
      (VectorBrownian.law N).map
        (fun ω => wienerVector t ω - wienerVector s ω) := by
  have hm : Measurable (fun ω : VectorBrownian.Space N =>
      wienerVector t ω - wienerVector s ω) :=
    (wienerVector_measurable t).sub (wienerVector_measurable s)
  change (VectorBrownian.law N).map
    (U ∘ (fun ω => wienerVector t ω - wienerVector s ω)) = _
  rw [← Measure.map_map U.continuous.measurable hm,
    wienerVector_increment_law s t hst]
  let c : ℝ := Real.sqrt ((t-s : ℝ≥0) : ℝ)
  have hfun : U ∘ (fun z : Vector N => c • z) =
      (fun z : Vector N => c • z) ∘ U := by
    funext z
    exact U.map_smul c z
  rw [Measure.map_map U.continuous.measurable (by fun_prop : Measurable (fun z : Vector N => c • z)),
    hfun, ← Measure.map_map (by fun_prop : Measurable (fun z : Vector N => c • z)) U.continuous.measurable,
    stdGaussian_map U]

end SlowEquilibration.SphericalWienerRotationFiniteLaw
