-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSource
public import SlowEquilibration.SphericalWeightedOverlapTail

/-! The literal smooth two-sided cap killing has an exponentially small
mean over an independent uniform axis for every fixed spherical spin. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 350000

/-- Uniform in the spherical spin, the physical cap killing is supported
on an exponentially rare set of independent axes. -/
theorem physical_capKilling_axis_mean_eventually_le
    {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ x : Vector N, ‖x‖^2 = (N : ℝ) →
      (∫ u : Vector N, PhysicalHitting.capKilling α u x ∂sphereLaw N) ≤
        C * Real.exp (-(N : ℝ) * α^2 / 64) := by
  obtain ⟨C,hC,hTail⟩ := sphere_weighted_overlap_tail_eventually_le
    (a := (0 : ℝ)) (b := 1/4) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C,hC,?_⟩
  filter_upwards [hTail,eventually_ge_atTop 1] with N ht hN
  intro x hx
  let A : Set (Vector N) := {u | α/4 < |overlap x u|}
  have hA : MeasurableSet A := by
    dsimp only [A]
    exact measurableSet_lt measurable_const (by unfold overlap; fun_prop)
  have hv : Continuous (fun u : Vector N => overlapValue u x) := by
    unfold overlapValue overlapLinear
    fun_prop
  have hκ : Continuous (fun u : Vector N => PhysicalHitting.capKilling α u x) := by
    exact ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hv).add
      ((SphericalCapCutoff.cutoff_contDiff _ _).continuous.comp hv.neg)
  have hiκ : Integrable (fun u : Vector N => PhysicalHitting.capKilling α u x)
      (sphereLaw N) := integrable_sphere_of_continuous hN hκ
  have hiA : Integrable (A.indicator (fun _ : Vector N => (1 : ℝ)))
      (sphereLaw N) := (integrable_const _).indicator hA
  have hdom (u : Vector N) : PhysicalHitting.capKilling α u x ≤
      A.indicator (fun _ => (1 : ℝ)) u := by
    have heq : overlapValue u x = overlap x u := by
      rw [overlapValue_eq,overlap,real_inner_comm]
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu]
      exact PhysicalHitting.capKilling_le_one hα u x
    · rw [Set.indicator_of_notMem hu]
      have hh : |overlapValue u x| ≤ α/4 := by
        rw [heq]
        exact le_of_not_gt hu
      rw [PhysicalHitting.capKilling_zero hα u x hh]
  have hmono := integral_mono hiκ hiA hdom
  have hb := ht x hx (α/4) (by positivity)
  simp only [zero_mul,Real.exp_zero] at hb
  calc
    _ ≤ ∫ u, A.indicator (fun _ => (1 : ℝ)) u ∂sphereLaw N := hmono
    _ ≤ C * Real.exp (-(N : ℝ) * α^2 / 64) := by
      convert hb using 1
      have he : -(N : ℝ) * α^2 / 64 =
          -(1/4 - 0) * (N : ℝ) * (α/4)^2 := by ring
      exact congrArg (fun t : ℝ => C * Real.exp t) he

end SlowEquilibration.ConditionedEntrance
