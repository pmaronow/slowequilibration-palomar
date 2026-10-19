-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWienerRotationFiniteGrid

/-! Orthogonal invariance of the full canonical vector Wiener path measure. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalWienerRotationPathLaw

open SphericalModel SphericalAging MeasureTheory ProbabilityTheory
open SlowEquilibration.SphericalWienerRotation
open SlowEquilibration.SphericalWienerRotationFiniteGrid
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem wienerVector_zero_ae {N : ℕ} :
    ∀ᵐ ω ∂(VectorBrownian.law N), wienerVector 0 ω = 0 := by
  have hi (i : Fin N) :
      ∀ᵐ ω ∂(VectorBrownian.law N), ω i 0 = 0 :=
    (VectorBrownian.coordinate_isPreBrownian i).hasLaw_eval 0
      |>.ae_eq_const_of_gaussianReal
  have hall : ∀ᵐ ω ∂(VectorBrownian.law N), ∀ i : Fin N, ω i 0 = 0 :=
    Filter.eventually_all.2 hi
  filter_upwards [hall] with ω hω
  ext i
  exact hω i

theorem wienerVector_finite_evaluations_rotation_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (I : Finset ℝ≥0) :
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => I.restrict
        (fun t => U (wienerVector t ω))) =
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => I.restrict
        (fun t => wienerVector t ω)) := by
  let τ : Fin (I.card + 1) → ℝ≥0 := I.ofFin'
  let A : (Fin I.card → Vector N) →L[ℝ] (I → Vector N) :=
    incrementsToRestrict ℝ I
  let Y : VectorBrownian.Space N → Fin I.card → Vector N :=
    fun ω j => wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω
  let YU : VectorBrownian.Space N → Fin I.card → Vector N :=
    fun ω j => U (wienerVector (τ j.succ) ω - wienerVector (τ j.castSucc) ω)
  have hτ : Monotone τ := Finset.monotone_ofFin' I
  have hY : Measurable Y := measurable_pi_iff.mpr fun j =>
    (wienerVector_measurable (τ j.succ)).sub
      (wienerVector_measurable (τ j.castSucc))
  have hYU : Measurable YU := measurable_pi_iff.mpr fun j =>
    U.continuous.measurable.comp
      ((wienerVector_measurable (τ j.succ)).sub
        (wienerVector_measurable (τ j.castSucc)))
  have h0 : ∀ᵐ ω ∂(VectorBrownian.law N), wienerVector 0 ω = 0 :=
    wienerVector_zero_ae
  have hU0 : ∀ᵐ ω ∂(VectorBrownian.law N),
      U (wienerVector 0 ω) = 0 := by
    filter_upwards [h0] with ω hω
    simp [hω]
  have hrec := incrementsToRestrict_increments_ofFin'_ae_eq_restrict
    (P := VectorBrownian.law N) ℝ h0 I
  have hrecU := incrementsToRestrict_increments_ofFin'_ae_eq_restrict
    (P := VectorBrownian.law N)
    (X := fun t (ω : VectorBrownian.Space N) => U (wienerVector t ω)) ℝ hU0 I
  have hrec' :
      (fun ω : VectorBrownian.Space N => I.restrict
        (fun t => wienerVector t ω)) =ᵐ[VectorBrownian.law N]
      A ∘ Y := hrec
  have hrecU' :
      (fun ω : VectorBrownian.Space N => I.restrict
        (fun t => U (wienerVector t ω))) =ᵐ[VectorBrownian.law N]
      A ∘ YU := by
    have heq : (fun ω : VectorBrownian.Space N =>
        fun j : Fin I.card =>
          U (wienerVector (τ j.succ) ω) -
            U (wienerVector (τ j.castSucc) ω)) = YU := by
      funext ω j
      exact (U.map_sub _ _).symm
    change (fun ω : VectorBrownian.Space N => I.restrict
      (fun t => U (wienerVector t ω))) =ᵐ[VectorBrownian.law N]
      A ∘ (fun ω : VectorBrownian.Space N =>
        fun j : Fin I.card =>
          U (wienerVector (τ j.succ) ω) -
            U (wienerVector (τ j.castSucc) ω)) at hrecU
    rw [heq] at hrecU
    exact hrecU
  calc
    _ = (VectorBrownian.law N).map (A ∘ YU) :=
      Measure.map_congr hrecU'
    _ = ((VectorBrownian.law N).map YU).map A := by
      exact (Measure.map_map A.continuous.measurable hYU).symm
    _ = ((VectorBrownian.law N).map Y).map A := by
      rw [show (VectorBrownian.law N).map YU =
        (VectorBrownian.law N).map Y from
          wienerVector_increments_grid_rotation_law U I.card τ hτ]
    _ = (VectorBrownian.law N).map (A ∘ Y) := by
      exact Measure.map_map A.continuous.measurable hY
    _ = _ := Measure.map_congr hrec'.symm

theorem wienerVector_process_rotation_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun t : ℝ≥0 =>
        U (wienerVector t ω)) =
    (VectorBrownian.law N).map
      (fun ω : VectorBrownian.Space N => fun t : ℝ≥0 =>
        wienerVector t ω) := by
  have hX : Measurable (fun ω : VectorBrownian.Space N =>
      fun t : ℝ≥0 => U (wienerVector t ω)) :=
    measurable_pi_iff.mpr fun t =>
      U.continuous.measurable.comp (wienerVector_measurable t)
  have hY : Measurable (fun ω : VectorBrownian.Space N =>
      fun t : ℝ≥0 => wienerVector t ω) :=
    measurable_pi_iff.mpr fun t => wienerVector_measurable t
  exact (map_eq_iff_forall_finset_map_restrict_eq
    hX.aemeasurable hY.aemeasurable).mpr fun I =>
      wienerVector_finite_evaluations_rotation_law U I

def wienerPathVector {N : ℕ}
    (ω : VectorBrownian.Space N) : C(ℝ≥0, Vector N) :=
  ⟨fun t => wienerVector t ω, wienerVector_continuous ω⟩

def wienerPathSplit {N : ℕ}
    (p : C(ℝ≥0, Vector N)) : VectorBrownian.Space N :=
  fun i => ⟨fun t => p t i,
    (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp p.continuous⟩

theorem wienerPathVector_measurable {N : ℕ} :
    Measurable (wienerPathVector (N := N)) := by
  rw [ContinuousMap.measurable_iff_eval]
  exact fun t => wienerVector_measurable t

theorem wienerPathSplit_measurable {N : ℕ} :
    Measurable (wienerPathSplit (N := N)) := by
  apply measurable_pi_iff.mpr
  intro i
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable.comp
    ((ContinuousMap.measurable_iff_eval
      (fun p : C(ℝ≥0, Vector N) => p)).mp measurable_id t)

theorem wienerPathSplit_wienerPathVector {N : ℕ} :
    wienerPathSplit (N := N) ∘ wienerPathVector = id := by
  funext ω i
  apply ContinuousMap.ext
  intro t
  rfl

theorem wienerPathVector_measure_ext {N : ℕ}
    {P Q : Measure (VectorBrownian.Space N)}
    (h : P.map (fun ω : VectorBrownian.Space N =>
        fun t : ℝ≥0 => wienerVector t ω) =
      Q.map (fun ω : VectorBrownian.Space N =>
        fun t : ℝ≥0 => wienerVector t ω)) : P = Q := by
  let E : C(ℝ≥0, Vector N) → ℝ≥0 → Vector N := fun p t => p t
  have hE : Measurable E := measurable_pi_iff.mpr fun t =>
    ((ContinuousMap.measurable_iff_eval
      (fun p : C(ℝ≥0, Vector N) => p)).mp measurable_id t)
  have hm : (inferInstance : MeasurableSpace C(ℝ≥0, Vector N)) =
      MeasurableSpace.pi.comap E := by
    calc
      _ = ⨆ t : ℝ≥0, (inferInstance : MeasurableSpace (Vector N)).comap
        (fun p : C(ℝ≥0, Vector N) => p t) :=
          ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp, Function.comp_def, E]
  have hpath : P.map wienerPathVector = Q.map wienerPathVector := by
    apply Measure.ext
    intro S hS
    change @MeasurableSet C(ℝ≥0, Vector N)
      (inferInstance : MeasurableSpace C(ℝ≥0, Vector N)) S at hS
    rw [hm] at hS
    rcases hS with ⟨T, hT, rfl⟩
    rw [← Measure.map_apply hE hT, ← Measure.map_apply hE hT,
      Measure.map_map hE wienerPathVector_measurable,
      Measure.map_map hE wienerPathVector_measurable]
    exact congrArg (fun M => M T) h
  have hh := congrArg (fun M => M.map wienerPathSplit) hpath
  rw [Measure.map_map wienerPathSplit_measurable wienerPathVector_measurable,
    Measure.map_map wienerPathSplit_measurable wienerPathVector_measurable] at hh
  simpa only [wienerPathSplit_wienerPathVector, Measure.map_id] using hh

theorem rotateWiener_law {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    (VectorBrownian.law N).map (rotateWiener U) = VectorBrownian.law N := by
  apply wienerPathVector_measure_ext
  have hm : Measurable (fun ω : VectorBrownian.Space N =>
      fun t : ℝ≥0 => wienerVector t ω) :=
    measurable_pi_iff.mpr fun t => wienerVector_measurable t
  rw [Measure.map_map hm (rotateWiener_measurable U)]
  change (VectorBrownian.law N).map
    (fun ω : VectorBrownian.Space N => fun t : ℝ≥0 =>
      wienerVector t (rotateWiener U ω)) = _
  have heval (ω : VectorBrownian.Space N) (t : ℝ≥0) :
      wienerVector t (rotateWiener U ω) = U (wienerVector t ω) := by
    ext i
    rfl
  simp only [heval]
  exact wienerVector_process_rotation_law U

end SlowEquilibration.SphericalWienerRotationPathLaw
