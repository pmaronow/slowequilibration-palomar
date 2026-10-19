-- SPDX-License-Identifier: Apache-2.0
module
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.LinearPMap

/-! A genuine transfer of an operator core under a bounded symmetric
perturbation and a unitary. Both operators are actual self-adjoint operators;
the differential identity on the first core implies the second core. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.UnitaryBoundedPerturbation
open Set
open scoped InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem hasCore_of_unitary_bounded_perturbation
    (A : E →ₗ.[ℝ] E) (B : F →ₗ.[ℝ] F) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (U : E ≃ₗᵢ[ℝ] F) (V : F →L[ℝ] F) (hV : V.IsSymmetric)
    (C : Submodule ℝ E) (hC : A.HasCore C)
    (hdom : ∀ x : C, U x ∈ B.domain)
    (hact : ∀ x : C, B ⟨U x,hdom x⟩ =
      U (A ⟨x,hC.le_domain x.property⟩) + V (U x)) :
    B.HasCore (C.map U.toLinearEquiv.toLinearMap) := by
  let D := C.map U.toLinearEquiv.toLinearMap
  let A₀ := A.domRestrict C
  let B₀ := B.domRestrict D
  have hAc : A₀.IsClosable := hA.isClosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hBc : B₀.IsClosable := hB.isClosed.isClosable.leIsClosable LinearPMap.domRestrict_le
  have hAD : A₀.graph.topologicalClosure = A.graph := by
    rw [hAc.graph_closure_eq_closure_graph,hC.closure_eq]
  have hBD : B₀.graph.topologicalClosure ≤ B.graph := by
    have h := Submodule.topologicalClosure_mono
      (LinearPMap.le_graph_of_le (show B₀ ≤ B from LinearPMap.domRestrict_le))
    rw [hB.isClosed.submodule_topologicalClosure_eq] at h
    exact h
  have hDdom : D ≤ B.domain := by
    rintro x ⟨y,hy,rfl⟩
    exact hdom ⟨y,hy⟩
  let Φ : E × E → F × F := fun z => (U z.1,U z.2+V (U z.1))
  have hΦ : Continuous Φ := by fun_prop
  have hbase : ∀ z∈A₀.graph, Φ z∈B₀.graph := by
    intro z hz
    obtain ⟨x,hx⟩ := (LinearPMap.mem_graph_iff' A₀).mp hz
    rw [← hx]
    have hxC : (x : E)∈C := x.property.1
    have hxB : U (x : E)∈B.domain := hdom ⟨x,hxC⟩
    have hxD : U (x : E)∈D := ⟨x,hxC,rfl⟩
    let y : B₀.domain := ⟨U (x : E),hxD,hxB⟩
    apply (LinearPMap.mem_graph_iff' B₀).mpr
    refine ⟨y,?_⟩
    change (U (x : E),B₀ y) = (U (x : E),U (A₀ x)+V (U (x : E)))
    congr 1
    change B ⟨U (x : E),hxB⟩ = U (A ⟨x,x.property.2⟩)+V (U (x : E))
    exact hact ⟨x,hxC⟩
  have hgraph : ∀ z∈A.graph, Φ z∈B₀.graph.topologicalClosure := by
    intro z hz
    rw [← hAD] at hz
    have hc : IsClosed {z | Φ z∈B₀.graph.topologicalClosure} :=
      B₀.graph.isClosed_topologicalClosure.preimage hΦ
    exact (show (A₀.graph.topologicalClosure : Set (E × E)) ⊆
      {z | Φ z∈B₀.graph.topologicalClosure} from
      closure_minimal (fun z hz => B₀.graph.le_topologicalClosure (hbase z hz)) hc) hz
  have hext (x : A.domain) : ∃ hx : U (x : E)∈B.domain,
      B ⟨U (x : E),hx⟩ = U (A x)+V (U (x : E)) := by
    have hz := hBD (hgraph ((x : E),A x) ((LinearPMap.mem_graph_iff' A).mpr ⟨x,rfl⟩))
    obtain ⟨y,hy1,hy2⟩ := (LinearPMap.mem_graph_iff B).mp hz
    change (y : F)=U (x : E) at hy1
    refine ⟨hy1 ▸ y.property,?_⟩
    convert hy2 using 1
    congr 1
    exact Subtype.ext hy1.symm
  have hBformal : B.IsFormalAdjoint B := by
    have ht := LinearPMap.adjoint_isFormalAdjoint (T := B) hB.dense_domain
    rwa [show B.adjoint=B from hB] at ht
  have hback (z : B.domain) : U.symm (z : F)∈A.domain := by
    have hm : U.symm (z : F)∈A.adjoint.domain := by
      apply A.mem_adjoint_domain_of_exists
      refine ⟨U.symm (B z - V (z : F)),fun x => ?_⟩
      obtain ⟨hx,hBx⟩ := hext x
      calc
        inner ℝ (U.symm (B z - V (z : F))) (x : E) =
            inner ℝ (B z - V (z : F)) (U (x : E)) := by
          rw [← U.inner_map_map]
          simp only [U.apply_symm_apply]
        _ = inner ℝ (z : F) (U (A x)) := by
          rw [inner_sub_left,hBformal z ⟨U (x : E),hx⟩,hBx,inner_add_right]
          have hv := hV (z : F) (U (x : E))
          change inner ℝ (V (z : F)) (U (x : E)) = inner ℝ (z : F) (V (U (x : E))) at hv
          linarith
        _ = inner ℝ (U.symm (z : F)) (A x) := by
          rw [← U.inner_map_map]
          simp only [U.apply_symm_apply]
    rwa [show A.adjoint=A from hA] at hm
  have hgraphs : B₀.graph.topologicalClosure=B.graph := by
    apply le_antisymm hBD
    intro z hz
    obtain ⟨y,hy⟩ := (LinearPMap.mem_graph_iff' B).mp hz
    let x : A.domain := ⟨U.symm (y : F),hback y⟩
    have hg := hgraph ((x : E),A x) ((LinearPMap.mem_graph_iff' A).mpr ⟨x,rfl⟩)
    obtain ⟨hx,hBx⟩ := hext x
    have hxval : U (x : E)=(y : F) := U.apply_symm_apply _
    have he : B y=U (A x)+V (U (x : E)) := by
      convert hBx using 1
      congr 1
      exact Subtype.ext hxval.symm
    have heq : Φ ((x : E),A x)=z := by
      rw [← hy]
      change (U (x : E),U (A x)+V (U (x : E)))=((y : F),B y)
      rw [← he,hxval]
    rwa [heq] at hg
  refine ⟨hDdom,?_⟩
  apply LinearPMap.eq_of_eq_graph
  exact hBc.graph_closure_eq_closure_graph.symm.trans hgraphs

end SlowEquilibration.UnitaryBoundedPerturbation
