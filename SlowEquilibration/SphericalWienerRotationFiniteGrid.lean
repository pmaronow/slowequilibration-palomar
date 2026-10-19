-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWienerRotationFiniteLaw
public import Mathlib.Probability.ProductMeasure

/-! Finite-grid orthogonal invariance for the genuine vector Wiener law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalWienerRotationFiniteGrid

open SphericalModel SphericalAging MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalWienerRotation
open SlowEquilibration.SphericalWienerRotationFiniteLaw
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem finite_product_transpose {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : ι → κ → Measure ℝ) [∀ i j, IsProbabilityMeasure (μ i j)] :
    (Measure.pi (fun i : ι => Measure.pi (fun j : κ => μ i j))).map
      (fun f : ι → κ → ℝ => fun j i => f i j) =
    Measure.pi (fun j : κ => Measure.pi (fun i : ι => μ i j)) := by
  let e : (ι × κ) ≃ (κ × ι) := Equiv.prodComm ι κ
  let ν : κ → ι → Measure ℝ := fun j i => μ i j
  have hC₁ :
      (Measure.pi (fun i : ι => Measure.pi (fun j : κ => μ i j))).map
        (MeasurableEquiv.curry ι κ ℝ).symm =
      Measure.pi (fun p : ι × κ => μ p.1 p.2) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry_symm μ)
  have hS :
      (Measure.pi (fun p : ι × κ => μ p.1 p.2)).map
        (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => ℝ) e) =
      Measure.pi (fun p : κ × ι => μ p.2 p.1) := by
    simpa [Measure.infinitePi_eq_pi, e] using
      (Measure.infinitePi_map_piCongrLeft (fun p : κ × ι => μ p.2 p.1) e)
  have hC₂ :
      (Measure.pi (fun p : κ × ι => μ p.2 p.1)).map
        (MeasurableEquiv.curry κ ι ℝ) =
      Measure.pi (fun j : κ => Measure.pi (fun i : ι => μ i j)) := by
    simpa only [Measure.infinitePi_eq_pi] using
      (Measure.infinitePi_map_curry ν)
  calc
    _ = ((Measure.pi (fun i : ι => Measure.pi (fun j : κ => μ i j))).map
      (MeasurableEquiv.curry ι κ ℝ).symm).map
      ((MeasurableEquiv.curry κ ι ℝ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => ℝ) e)) := by
      rw [Measure.map_map
        ((MeasurableEquiv.curry κ ι ℝ).measurable.comp
          (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => ℝ) e).measurable)
        (MeasurableEquiv.curry ι κ ℝ).symm.measurable]
      congr 1
    _ = _ := by
      rw [hC₁, ← Measure.map_map (MeasurableEquiv.curry κ ι ℝ).measurable
        (MeasurableEquiv.piCongrLeft (fun _ : κ × ι => ℝ) e).measurable,
        hS, hC₂]

theorem wiener_raw_increments_grid_law {N : ℕ} (n : ℕ)
    (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun j : Fin n => fun i : Fin N =>
        ω i (τ j.succ) - ω i (τ j.castSucc)) =
    Measure.pi (fun j : Fin n => Measure.pi (fun _ : Fin N =>
      gaussianReal 0 (τ j.succ - τ j.castSucc))) := by
  let X : VectorBrownian.Path → Fin n → ℝ := fun η j =>
    η (τ j.succ) - η (τ j.castSucc)
  have hX : Measurable X := measurable_pi_iff.mpr fun j =>
    (VectorBrownian.scalar_eval_measurable (τ j.succ)).sub
      (VectorBrownian.scalar_eval_measurable (τ j.castSucc))
  have hscalar : VectorBrownian.pathLaw.map X =
      Measure.pi (fun j : Fin n =>
        gaussianReal 0 (τ j.succ - τ j.castSucc)) := by
    have hind := VectorBrownian.scalar_isPreBrownian.hasIndepIncrements n τ hτ
    have hh := hind.map_fun_eq_pi_map (fun (j : Fin n) =>
      ((VectorBrownian.scalar_eval_measurable (τ j.succ)).sub
        (VectorBrownian.scalar_eval_measurable (τ j.castSucc))).aemeasurable)
    change VectorBrownian.pathLaw.map X =
      Measure.pi (fun j : Fin n =>
        VectorBrownian.pathLaw.map
          (fun η : VectorBrownian.Path =>
            η (τ j.succ) - η (τ j.castSucc))) at hh
    rw [hh]
    congr 1
    funext j
    have ht : τ j.castSucc ≤ τ j.succ := hτ (Fin.castSucc_le_succ j)
    have hv : nndist ((τ j.succ : ℝ≥0) : ℝ)
        ((τ j.castSucc : ℝ≥0) : ℝ) = τ j.succ - τ j.castSucc := by
      ext
      simp only [coe_nndist, Real.dist_eq, abs_of_nonneg
        (sub_nonneg.mpr (show (τ j.castSucc : ℝ) ≤ τ j.succ from ht)),
        NNReal.coe_sub ht]
    have hl := VectorBrownian.scalar_isPreBrownian.hasLaw_sub
      (τ j.succ) (τ j.castSucc)
    convert hl.map_eq using 1
    congr 1
    exact hv.symm
  have hpi :
      (VectorBrownian.law N).map
        (fun ω : VectorBrownian.Space N => fun i : Fin N => X (ω i)) =
      Measure.pi (fun _ : Fin N => VectorBrownian.pathLaw.map X) := by
    exact Measure.pi_map_pi (fun _ : Fin N => hX.aemeasurable)
  let μ : Fin N → Fin n → Measure ℝ := fun _ j =>
    gaussianReal 0 (τ j.succ - τ j.castSucc)
  have htranspose := finite_product_transpose μ
  calc
    (VectorBrownian.law N).map
        (fun ω : VectorBrownian.Space N => fun j : Fin n => fun i : Fin N =>
          ω i (τ j.succ) - ω i (τ j.castSucc)) =
      ((VectorBrownian.law N).map
        (fun ω : VectorBrownian.Space N => fun i : Fin N => X (ω i))).map
        (fun f : Fin N → Fin n → ℝ => fun j i => f i j) := by
      change (VectorBrownian.law N).map
        ((fun f : Fin N → Fin n → ℝ => fun j i => f i j) ∘
          (fun ω : VectorBrownian.Space N => fun i : Fin N => X (ω i))) = _
      have hG : Measurable (fun ω : VectorBrownian.Space N =>
          fun i : Fin N => X (ω i)) :=
        measurable_pi_iff.mpr fun i => hX.comp (measurable_pi_apply i)
      have hT : Measurable (fun f : Fin N → Fin n → ℝ =>
          fun j i => f i j) := by fun_prop
      exact (Measure.map_map hT hG).symm
    _ = (Measure.pi (fun i : Fin N => Measure.pi
        (fun j : Fin n => gaussianReal 0 (τ j.succ - τ j.castSucc)))).map
        (fun f : Fin N → Fin n → ℝ => fun j i => f i j) := by
      rw [hpi,hscalar]
    _ = _ := htranspose

theorem wienerVector_increments_grid_law {N : ℕ} (n : ℕ)
    (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun j : Fin n =>
        wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω) =
    Measure.pi (fun j : Fin n =>
      (stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z)) := by
  let F : (Fin N → ℝ) → Vector N := WithLp.toLp 2
  let G : (Fin n → Fin N → ℝ) → (Fin n → Vector N) := fun f j => F (f j)
  have hF : Measurable F := (PiLp.continuous_toLp 2 _).measurable
  have hG : Measurable G := measurable_pi_iff.mpr fun j =>
    hF.comp (measurable_pi_apply j)
  have hraw : Measurable (fun ω : VectorBrownian.Space N =>
      fun j : Fin n => fun i : Fin N =>
        ω i (τ j.succ) - ω i (τ j.castSucc)) :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
      (VectorBrownian.coordinate_measurable i (τ j.succ)).sub
        (VectorBrownian.coordinate_measurable i (τ j.castSucc))
  have hfactor (j : Fin n) :
      (Measure.pi (fun _ : Fin N =>
        gaussianReal 0 (τ j.succ - τ j.castSucc))).map F =
      (stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z) := by
    have hst : τ j.castSucc ≤ τ j.succ := hτ (Fin.castSucc_le_succ j)
    rw [← wiener_raw_vector_increment_law (N := N)
      (τ j.castSucc) (τ j.succ) hst]
    have hm : Measurable (fun ω : VectorBrownian.Space N =>
        fun i : Fin N => ω i (τ j.succ) - ω i (τ j.castSucc)) :=
      measurable_pi_iff.mpr fun i =>
        (VectorBrownian.coordinate_measurable i (τ j.succ)).sub
          (VectorBrownian.coordinate_measurable i (τ j.castSucc))
    rw [Measure.map_map hF hm]
    exact wienerVector_increment_law (τ j.castSucc) (τ j.succ) hst
  calc
    _ = ((VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun j : Fin n => fun i : Fin N =>
        ω i (τ j.succ) - ω i (τ j.castSucc))).map G := by
      rw [Measure.map_map hG hraw]
      rfl
    _ = (Measure.pi (fun j : Fin n => Measure.pi (fun _ : Fin N =>
        gaussianReal 0 (τ j.succ - τ j.castSucc)))).map G := by
      rw [wiener_raw_increments_grid_law n τ hτ]
    _ = Measure.pi (fun j : Fin n =>
      (Measure.pi (fun _ : Fin N =>
        gaussianReal 0 (τ j.succ - τ j.castSucc))).map F) := by
      exact Measure.pi_map_pi (fun _ : Fin n => hF.aemeasurable)
    _ = _ := by simp only [hfactor]

theorem wienerVector_increments_grid_rotation_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (n : ℕ)
    (τ : Fin (n+1) → ℝ≥0) (hτ : Monotone τ) :
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun j : Fin n =>
        U (wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω)) =
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun j : Fin n =>
        wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω) := by
  let X : VectorBrownian.Space N → Fin n → Vector N := fun ω j =>
    wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω
  let R : (Fin n → Vector N) → Fin n → Vector N := fun f j => U (f j)
  have hX : Measurable X := measurable_pi_iff.mpr fun j =>
    (wienerVector_measurable (τ j.succ)).sub
      (wienerVector_measurable (τ j.castSucc))
  have hR : Measurable R := measurable_pi_iff.mpr fun j =>
    U.continuous.measurable.comp (measurable_pi_apply j)
  have hfactor (j : Fin n) :
      ((stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z)).map U =
      (stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z) := by
    have hst : τ j.castSucc ≤ τ j.succ := hτ (Fin.castSucc_le_succ j)
    rw [← wienerVector_increment_law (N := N)
      (τ j.castSucc) (τ j.succ) hst]
    have hm : Measurable (fun ω : VectorBrownian.Space N =>
        wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω) :=
      (wienerVector_measurable (τ j.succ)).sub
        (wienerVector_measurable (τ j.castSucc))
    rw [Measure.map_map U.continuous.measurable hm]
    exact wienerVector_increment_rotation_law U
      (τ j.castSucc) (τ j.succ) hst
  calc
    _ = ((VectorBrownian.law N).map X).map R := by
      rw [Measure.map_map hR hX]
      rfl
    _ = (Measure.pi (fun j : Fin n =>
      (stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z))).map R := by
      rw [wienerVector_increments_grid_law n τ hτ]
    _ = Measure.pi (fun j : Fin n =>
      ((stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z)).map U) := by
      exact Measure.pi_map_pi (fun _ : Fin n => U.continuous.measurable.aemeasurable)
    _ = Measure.pi (fun j : Fin n =>
      (stdGaussian (Vector N)).map
        (fun z => Real.sqrt (((τ j.succ - τ j.castSucc : ℝ≥0) : ℝ)) • z)) := by
      simp only [hfactor]
    _ = _ := (wienerVector_increments_grid_law n τ hτ).symm

end SlowEquilibration.SphericalWienerRotationFiniteGrid
