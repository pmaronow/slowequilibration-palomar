-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-! Uniform density of the linear span of constants and genuine outside
resolvents on a compact real interval. Repeated poles are limits of distinct
poles, so the closed linear span is an algebra and Stone--Weierstrass applies. -/

@[expose] public section
namespace SlowEquilibration.ResolventDensity

noncomputable section
open Set Filter ContinuousMap
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

abbrev K := Icc (-2 : ℝ) 2
abbrev Pole := Ioi (2 : ℝ)

instance : CompactSpace K := isCompact_iff_compactSpace.mp isCompact_Icc

def resolvent (a : Pole) : C(K,ℝ) where
  toFun x := (a.val-x.val)⁻¹
  continuous_toFun := (continuous_const.sub continuous_subtype_val).inv₀ (by
    intro x
    exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt x.prop.2 a.prop)))

lemma resolvent_continuous : Continuous resolvent := by
  let R : C(Pole × K,ℝ) := ⟨fun p => (p.1.val-p.2.val)⁻¹,
    ((continuous_subtype_val.comp continuous_fst).sub
      (continuous_subtype_val.comp continuous_snd)).inv₀ (by
      intro p
      exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt p.2.prop.2 p.1.prop)))⟩
  exact R.curry.continuous

def generators : Set C(K,ℝ) := {f | f=1 ∨ ∃ a : Pole, f=resolvent a}

def spanClosure : Submodule ℝ C(K,ℝ) := (Submodule.span ℝ generators).topologicalClosure

lemma spanClosure_closed : IsClosed (spanClosure : Set C(K,ℝ)) :=
  Submodule.isClosed_topologicalClosure _

lemma generator_mem {f : C(K,ℝ)} (hf : f∈generators) : f∈spanClosure :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span hf)

lemma one_mem : (1:C(K,ℝ))∈spanClosure := generator_mem (Or.inl rfl)
lemma resolvent_mem (a : Pole) : resolvent a∈spanClosure := generator_mem (Or.inr ⟨a,rfl⟩)

lemma resolvent_mul_distinct (a b : Pole) (hab : a.val≠b.val) :
    resolvent a*resolvent b∈spanClosure := by
  have he : resolvent a*resolvent b=(1/(b.val-a.val)) • (resolvent a-resolvent b) := by
    ext x
    change (a.val-x.val)⁻¹*(b.val-x.val)⁻¹=(1/(b.val-a.val))*
      ((a.val-x.val)⁻¹-(b.val-x.val)⁻¹)
    have ha : a.val-x.val≠0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt x.prop.2 a.prop))
    have hb : b.val-x.val≠0 := ne_of_gt (sub_pos.mpr (lt_of_le_of_lt x.prop.2 b.prop))
    have hd : b.val-a.val≠0 := sub_ne_zero.mpr hab.symm
    field_simp
    ring
  rw [he]
  exact spanClosure.smul_mem _ (spanClosure.sub_mem (resolvent_mem a) (resolvent_mem b))

lemma resolvent_mul (a b : Pole) : resolvent a*resolvent b∈spanClosure := by
  by_cases hab : a.val=b.val
  · have heq : a=b := Subtype.ext hab
    subst b
    let bs : ℕ → Pole := fun n => ⟨a.val+1/(n+1 : ℝ),by
      have hp : 0<1/(n+1 : ℝ) := by positivity
      exact lt_add_of_lt_of_nonneg a.prop hp.le⟩
    have hb : Tendsto bs atTop (𝓝 a) := by
      apply tendsto_subtype_rng.mpr
      have hn : Tendsto (fun n : ℕ => (n+1 : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1:ℝ)))
      simpa only [bs,add_zero] using tendsto_const_nhds.add (hn.const_div_atTop 1)
    have ht := (tendsto_const_nhds (x := resolvent a)).mul (resolvent_continuous.tendsto a |>.comp hb)
    exact spanClosure_closed.mem_of_tendsto ht (Eventually.of_forall fun n =>
      resolvent_mul_distinct a (bs n) (by
        have hp : 0<1/(n+1 : ℝ) := by positivity
        change a.val≠a.val+1/(n+1 : ℝ)
        linarith))
  · exact resolvent_mul_distinct a b hab

lemma generators_mul {f g : C(K,ℝ)} (hf : f∈generators) (hg : g∈generators) :
    f*g∈spanClosure := by
  rcases hf with rfl | ⟨a,rfl⟩
  · simpa using generator_mem hg
  · rcases hg with rfl | ⟨b,rfl⟩
    · simpa using resolvent_mem a
    · exact resolvent_mul a b

lemma spans_mul {f g : C(K,ℝ)} (hf : f∈Submodule.span ℝ generators)
    (hg : g∈Submodule.span ℝ generators) : f*g∈spanClosure := by
  exact LinearMap.BilinMap.apply_apply_mem_of_mem_span
    spanClosure generators generators (LinearMap.mul ℝ C(K,ℝ)) (fun _ hf _ hg => generators_mul hf hg) f g hf hg

lemma spanClosure_mul {f g : C(K,ℝ)} (hf : f∈spanClosure) (hg : g∈spanClosure) :
    f*g∈spanClosure := by
  have hleft (g : C(K,ℝ)) (hg : g∈Submodule.span ℝ generators) :
      ∀ f∈spanClosure,f*g∈spanClosure := by
    let L : C(K,ℝ) →L[ℝ] C(K,ℝ) := (ContinuousLinearMap.mul ℝ C(K,ℝ)).flip g
    let T : Submodule ℝ C(K,ℝ) := spanClosure.comap L.toLinearMap
    have hT : IsClosed (T : Set C(K,ℝ)) := spanClosure_closed.preimage L.continuous
    have hh : Submodule.span ℝ generators≤T := by
      intro f hf
      exact spans_mul hf hg
    exact Submodule.topologicalClosure_minimal _ hh hT
  let L : C(K,ℝ) →L[ℝ] C(K,ℝ) := ContinuousLinearMap.mul ℝ C(K,ℝ) f
  let T : Submodule ℝ C(K,ℝ) := spanClosure.comap L.toLinearMap
  have hT : IsClosed (T : Set C(K,ℝ)) := spanClosure_closed.preimage L.continuous
  have hh : Submodule.span ℝ generators≤T := by
    intro g hg
    exact hleft g hg f hf
  exact Submodule.topologicalClosure_minimal _ hh hT hg

def resolventAlgebra : Subalgebra ℝ C(K,ℝ) where
  carrier := spanClosure
  zero_mem' := spanClosure.zero_mem
  one_mem' := one_mem
  add_mem' := spanClosure.add_mem
  mul_mem' := spanClosure_mul
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    change (r • (1:C(K,ℝ)))∈spanClosure
    exact spanClosure.smul_mem r one_mem

lemma resolventAlgebra_separates : resolventAlgebra.SeparatesPoints := by
  intro x y hxy
  let a : Pole := ⟨3,by norm_num⟩
  refine ⟨resolvent a,⟨resolvent a,resolvent_mem a,rfl⟩,?_⟩
  intro he
  change (3-x.val)⁻¹=(3-y.val)⁻¹ at he
  have hh := inv_injective he
  exact hxy (Subtype.ext (by linarith))

/-- Every real continuous function on the actual spectral interval belongs
to the closed linear span of constants and outside resolvents. -/
theorem spanClosure_eq_top : spanClosure=⊤ := by
  have hc : IsClosed (resolventAlgebra : Set C(K,ℝ)) := spanClosure_closed
  have ht := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints
    resolventAlgebra resolventAlgebra_separates
  have he : resolventAlgebra.topologicalClosure=resolventAlgebra :=
    le_antisymm (Subalgebra.topologicalClosure_minimal le_rfl hc)
      (Subalgebra.le_topologicalClosure resolventAlgebra)
  rw [he] at ht
  exact congrArg Subalgebra.toSubmodule ht

end
end SlowEquilibration.ResolventDensity
