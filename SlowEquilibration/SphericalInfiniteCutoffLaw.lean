-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalInfinitePressureTruncation
public import SlowEquilibration.InfiniteMixtureFiniteCutoff
public import SlowEquilibration.SphericalParisiBound

/-! Finite canonical mixtures realized as literal projections of the original
infinite disorder. Field equality holds pathwise, not merely in covariance. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open MeasureTheory ProbabilityTheory SphericalModel
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transporting the degree index preserves every ordered tensor coordinate. -/
def castDegree {N a b : ℕ} (h : a=b) : SphericalAging.FiniteModel.Disorder N a →
    SphericalAging.FiniteModel.Disorder N b := h ▸ id

theorem castDegree_measurable {N a b : ℕ} (h : a=b) : Measurable (castDegree (N := N) h) := by
  subst b
  exact measurable_id

theorem castDegree_hasLaw {N a b : ℕ} (h : a=b) : HasLaw (castDegree (N := N) h)
    (SphericalAging.FiniteModel.disorderLaw N b) (SphericalAging.FiniteModel.disorderLaw N a) := by
  subst b
  exact ⟨measurable_id.aemeasurable,Measure.map_id⟩

theorem Hamiltonian_castDegree {N a b : ℕ} (h : a=b)
    (J : SphericalAging.FiniteModel.Disorder N a) (x : Vector N) :
    SphericalAging.FiniteModel.Hamiltonian N b (castDegree h J) x=
      SphericalAging.FiniteModel.Hamiltonian N a J x := by subst b;rfl

/-- Every canonical finite disorder block is taken from its own original degree. -/
def finiteDisorder {N : ℕ} (P : ℕ) (J : Disorder N) : SphericalModel.Disorder N P :=
  fun p => castDegree (Nat.sub_add_cancel p.property) (J (p.val.val-2))

theorem finiteDisorder_measurable {N P : ℕ} : Measurable (finiteDisorder (N := N) P) := by
  apply measurable_pi_lambda
  intro p
  exact (castDegree_measurable _).comp (measurable_pi_apply _)

theorem finiteDisorder_hasLaw {N P : ℕ} : HasLaw (finiteDisorder (N := N) P)
    (SphericalModel.disorderLaw N P) (disorderLaw N) := by
  have hp : Function.Injective (fun p : Degree P => p.val.val-2) := by
    intro p q hpq
    apply Subtype.ext
    apply Fin.ext
    change p.val.val-2=q.val.val-2 at hpq
    have hpl := p.property
    have hql := q.property
    omega
  have hi := (independent_degrees N).precomp hp
  have hic := hi.comp (fun p : Degree P => castDegree (N := N) (Nat.sub_add_cancel p.property))
    (fun p => castDegree_measurable _)
  exact iIndepFun.hasLaw_pi (fun p => (castDegree_hasLaw _).comp (degree_hasLaw (p.val.val-2))) hic

def degreeEquiv {P : ℕ} (hP : 2≤P) : Degree P ≃ Fin (P-1) where
  toFun p := ⟨p.val.val-2,by have hp := p.val.isLt;have hl := p.property;omega⟩
  invFun q := ⟨⟨q.val+2,by have hq := q.isLt;omega⟩,by change 2≤q.val+2;omega⟩
  left_inv p := by apply Subtype.ext;apply Fin.ext;have hp := p.property;dsimp;omega
  right_inv q := by apply Fin.ext;dsimp;omega

theorem finiteCutoff_maxDegree_le (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) : (μ.finiteCutoff P hP).maxDegree≤P := by
  let ν := μ.finiteCutoff P hP
  have hm := Finset.max'_mem ν.coeff.support ν.support_nonempty
  have hh := Finsupp.mem_support_iff.mp hm
  change (μ.finiteCutoff P hP).coeff ν.maxDegree≠0 at hh
  rw [InfiniteMixture.finiteCutoff_coeff] at hh
  by_contra he
  simp [show ¬ν.maxDegree≤P by exact he] at hh

/-- Literal original field equality for the actual nonzero canonical cutoff. -/
theorem finiteCutoff_field {N : ℕ} (μ : InfiniteMixture) (P : ℕ)
    (hP : ∃ p,p≤P ∧ 0<μ.coeff p) (J : Disorder N) (x : Vector N) :
    fieldOfMixture (μ.finiteCutoff P hP) (finiteDisorder (μ.finiteCutoff P hP).maxDegree J) x=
      partialField μ (P-1) J x := by
  let ν := μ.finiteCutoff P hP
  have hmax : ν.maxDegree≤P := finiteCutoff_maxDegree_le μ P hP
  have htwo : 2≤ν.maxDegree := ν.minDegree_ge_two.trans
    (Finset.min'_le_max' ν.coeff.support ν.support_nonempty)
  have hsum : fieldOfMixture ν (finiteDisorder ν.maxDegree J) x=
      ∑ i : Fin (ν.maxDegree-1),block μ i.val J x := by
    rw [← (degreeEquiv htwo).sum_comp (fun i : Fin (ν.maxDegree-1) => block μ i.val J x)]
    unfold fieldOfMixture SphericalModel.field
    apply Finset.sum_congr rfl
    intro p _
    change Real.sqrt (ν.coeff p.val.val)*
      SphericalAging.FiniteModel.Hamiltonian N p.val.val
        (castDegree (Nat.sub_add_cancel p.property) (J (p.val.val-2))) x=block μ (p.val.val-2) J x
    rw [Hamiltonian_castDegree]
    dsimp [ν]
    rw [InfiniteMixture.finiteCutoff_coeff,if_pos (by have hp := p.val.isLt;omega)]
    simp only [block,Nat.sub_add_cancel p.property]
  rw [hsum,Fin.sum_univ_eq_sum_range (fun q => block μ q J x) (ν.maxDegree-1)]
  unfold partialField
  apply Finset.sum_subset
  · intro q hq
    simp only [Finset.mem_range] at hq ⊢
    omega
  · intro q hq hnq
    have hc : μ.coeff (q+2)=0 := by
      have hqP : q+2≤P := by simp only [Finset.mem_range] at hq;omega
      have hqmax : ν.maxDegree<q+2 := by simp only [Finset.mem_range,not_lt] at hnq;omega
      have hcut : ν.coeff (q+2)=0 := by
        by_contra hne
        have hle := (ν.degree_bounds (Finsupp.mem_support_iff.mpr hne)).2
        omega
      simpa only [ν,InfiniteMixture.finiteCutoff_coeff,if_pos hqP] using hcut
    simp [block,hc]

end SlowEquilibration.SphericalInfiniteModel
