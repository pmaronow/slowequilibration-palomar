-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionFiberCardinalityBorel
public import Mathlib.Order.PiLex

@[expose] public section

/-! A canonical Borel lexicographic order on the finite-dimensional physical
sphere, used to enumerate each finite critical-center fiber uniquely. -/

namespace SlowEquilibration.SourceReductionPhysicalLexOrder
noncomputable section
open Set MeasureTheory SphericalModel SphericalRotationCovariance
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

def physicalLexKey {N : ℕ} (u : PhysicalSphere N) : Lex (Fin N → ℝ) :=
  toLex (fun i => u.1 i)

theorem physicalLexKey_injective {N : ℕ} :
    Function.Injective (physicalLexKey (N := N)) := by
  intro u v h
  apply Subtype.ext
  apply PiLp.ext
  intro i
  exact congrArg (fun f : Lex (Fin N → ℝ) => ofLex f i) h

noncomputable abbrev physicalLexOrder (N : ℕ) : LinearOrder (PhysicalSphere N) :=
  LinearOrder.lift' (physicalLexKey (N := N)) physicalLexKey_injective

def physicalLexBefore {N : ℕ} (u v : PhysicalSphere N) : Prop :=
  Pi.Lex (· < ·) (· < ·) (fun i : Fin N => u.1 i) (fun i => v.1 i)

theorem physicalLexBefore_iff_lt {N : ℕ} (u v : PhysicalSphere N) :
    physicalLexBefore u v ↔ @LT.lt (PhysicalSphere N) (physicalLexOrder N).toLT u v := by
  rfl

theorem physicalLexBefore_measurableSet {N : ℕ} :
    MeasurableSet {z : PhysicalSphere N × PhysicalSphere N |
      physicalLexBefore z.1 z.2} := by
  have hEq : {z : PhysicalSphere N × PhysicalSphere N |
      physicalLexBefore z.1 z.2} =
      ⋃ i : Fin N,
        {z | (∀ j : Fin N, j < i → z.1.1 j = z.2.1 j) ∧
          z.1.1 i < z.2.1 i} := by
    ext z
    simp only [physicalLexBefore,Pi.Lex,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [hEq]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.inter
  · have hForall : MeasurableSet
        (⋂ j : Fin N,
          {z : PhysicalSphere N × PhysicalSphere N |
            j < i → z.1.1 j = z.2.1 j}) := by
      apply MeasurableSet.iInter
      intro j
      by_cases hji : j < i
      · have hc₁ : Continuous (fun z : PhysicalSphere N × PhysicalSphere N => z.1.1 j) := by
          fun_prop
        have hc₂ : Continuous (fun z : PhysicalSphere N × PhysicalSphere N => z.2.1 j) := by
          fun_prop
        simpa [hji] using (isClosed_eq hc₁ hc₂).measurableSet
      · simp [hji]
    have hEq : {z : PhysicalSphere N × PhysicalSphere N |
        ∀ j : Fin N, j < i → z.1.1 j = z.2.1 j} =
        ⋂ j : Fin N,
          {z | j < i → z.1.1 j = z.2.1 j} := by
      ext z
      simp only [Set.mem_iInter,Set.mem_ofPred_eq]
    change MeasurableSet {z : PhysicalSphere N × PhysicalSphere N |
      ∀ j : Fin N, j < i → z.1.1 j = z.2.1 j}
    rw [hEq]
    exact hForall
  · have hc₁ : Continuous (fun z : PhysicalSphere N × PhysicalSphere N => z.1.1 i) := by
      fun_prop
    have hc₂ : Continuous (fun z : PhysicalSphere N × PhysicalSphere N => z.2.1 i) := by
      fun_prop
    exact (isOpen_lt hc₁ hc₂).measurableSet

end
end SlowEquilibration.SourceReductionPhysicalLexOrder
