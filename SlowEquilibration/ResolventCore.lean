module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ResolventOperator
public import Mathlib.Topology.Algebra.Module.LinearPMap

@[expose] public section

/-! # Genuine operator cores from proved dense resolvent forcing -/

namespace SlowEquilibration.ResolventOperator
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open Set Filter
open scoped Topology InnerProductSpace

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [AddCommGroup D] [Module ℝ D]

/-- A literal value core whose actual resolvent forcings are dense is an
operator core for the true inverse-shift operator. Graph closure and the
self-adjoint closure are conclusions, rather than inputs. -/
theorem inverseShift_hasCore_of_dense_forcing (R : E →L[ℝ] E) (hR : Function.Injective R)
    (hS : R.IsSymmetric) (V : D →ₗ[ℝ] E) (K : D → E)
    (hRK : ∀ d, R (K d) = V d) (hK : DenseRange K) :
    (inverseShift R hR).HasCore (LinearMap.range V) := by
  let A := inverseShift R hR
  let S := LinearMap.range V
  let B := A.domRestrict S
  let Φ : E →L[ℝ] E × E := R.prod (ContinuousLinearMap.id ℝ E - R)
  have hclosed : A.IsClosed := (inverseShift_selfAdjoint R hR hS).isClosed
  have hB : B ≤ A := LinearPMap.domRestrict_le
  have hbc : B.IsClosable := hclosed.isClosable.leIsClosable hB
  have hdom : S ≤ A.domain := by
    rintro x ⟨d, rfl⟩
    exact ⟨K d, hRK d⟩
  have hΦd (d : D) : Φ (K d) ∈ B.graph := by
    have hsm : R (K d) ∈ S := by rw [hRK d]; exact ⟨d, rfl⟩
    let u : B.domain := ⟨R (K d), hsm, ⟨K d, rfl⟩⟩
    have he : B u = K d - R (K d) := by
      rw [show B u = A ⟨R (K d), ⟨K d, rfl⟩⟩ from LinearPMap.domRestrict_apply rfl]
      exact inverseShift_apply R hR (K d)
    apply (LinearPMap.mem_graph_iff' B).mpr
    exact ⟨u, by change (R (K d), B u) = (R (K d), K d - R (K d)); rw [he]⟩
  have hΦ (x : E) : Φ x ∈ B.graph.topologicalClosure := by
    exact hK.induction_on (p := fun x => Φ x ∈ B.graph.topologicalClosure) x
      ((Submodule.isClosed_topologicalClosure B.graph).preimage Φ.continuous)
      (fun d => B.graph.le_topologicalClosure (hΦd d))
  have hgraph : B.graph.topologicalClosure = A.graph := by
    apply le_antisymm
    · have hm := Submodule.topologicalClosure_mono (LinearPMap.le_graph_of_le hB)
      rw [hclosed.submodule_topologicalClosure_eq] at hm
      exact hm
    · intro x hx
      obtain ⟨u, hu⟩ := (LinearPMap.mem_graph_iff' A).mp hx
      obtain ⟨f, hf⟩ := u.property
      have he : u = (⟨R f, ⟨f, rfl⟩⟩ : A.domain) := Subtype.ext hf.symm
      have hxΦ : Φ f = x := by
        rw [← hu, he]
        change (R f, f - R f) = (R f, A ⟨R f, ⟨f, rfl⟩⟩)
        rw [inverseShift_apply]
      rw [← hxΦ]
      exact hΦ f
  refine ⟨hdom, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  exact (hbc.graph_closure_eq_closure_graph.symm).trans hgraph

end
end SlowEquilibration.ResolventOperator
