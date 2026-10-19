-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PureTensorJetFeatures
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Algebra.BigOperators.Fin

/-! Exact ordered-tensor realization of finite sums of products of
linear forms. This is the physical polynomial family used to approximate
the smooth two-variable entrance cutoff. No covariance-matching field is
substituted for its actual coefficients. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance.TensorPolynomial
open SphericalModel PureTensorJetFeatures
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N P : ℕ}

def productDisorder {p : ℕ} (b : ℝ) (v : Fin p → Vector N) :
    SphericalAging.FiniteModel.Disorder N p :=
  fun I => (SphericalAging.FiniteModel.normalization N p)⁻¹ * b * tensorFeature v I

theorem Hamiltonian_productDisorder (hN : 1 ≤ N) {p : ℕ} (b : ℝ)
    (v : Fin p → Vector N) (x : Vector N) :
    SphericalAging.FiniteModel.Hamiltonian N p (productDisorder b v) x =
      b * ∏ k : Fin p, inner ℝ (v k) x := by
  have hn : SphericalAging.FiniteModel.normalization N p ≠ 0 := by
    apply ne_of_gt
    exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (show 0 < N by omega)) _
  have he : (∑ I : SphericalAging.FiniteModel.TensorIndex N p,
      tensorFeature v I * SphericalAging.FiniteModel.tensorMonomial x I) =
      inner ℝ (tensorFeature v) (tensorFeature (fun _ : Fin p => x)) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
      tensorFeature_apply,SphericalAging.FiniteModel.tensorMonomial]
    apply Finset.sum_congr rfl
    intro I _
    ring
  unfold SphericalAging.FiniteModel.Hamiltonian productDisorder
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum,← Finset.mul_sum,he,tensorFeature_inner]
  field_simp

/-- A literal finite product of ordinary ambient linear forms, in an
allowed physical tensor degree. -/
structure Atom (N P : ℕ) where
  degree : Degree P
  coefficient : ℝ
  factors : Fin degree.val.val → Vector N

def Atom.value (a : Atom N P) (x : Vector N) : ℝ :=
  a.coefficient * ∏ k : Fin a.degree.val.val, inner ℝ (a.factors k) x

def Atom.disorder (a : Atom N P) : Disorder N P := fun p =>
  if h : p=a.degree then
    h.symm ▸ productDisorder a.coefficient a.factors
  else 0

theorem Atom.field_eq (hN : 1 ≤ N) (a : Atom N P) (x : Vector N) :
    field (fun _ : Degree P => 1) a.disorder x=a.value x := by
  classical
  unfold field
  simp only [Real.sqrt_one,one_mul]
  rw [Finset.sum_eq_single a.degree]
  · simpa [blockField,Atom.disorder,Atom.value] using
      Hamiltonian_productDisorder hN a.coefficient a.factors x
  · intro p _ hp
    simp only [blockField,Atom.disorder,dite_eq_right hp]
    rw [← pureFieldCLM_apply]
    exact map_zero _
  · simp

def atomBank {ι : Type*} [Fintype ι] (a : ι → Atom N P) : Disorder N P :=
  ∑ i, (a i).disorder

/-- Actual equality with the full finite mixed ordered-tensor Hamiltonian,
including the normalization of every degree block. -/
theorem atomBank_field (hN : 1 ≤ N) {ι : Type*} [Fintype ι]
    (a : ι → Atom N P) (x : Vector N) :
    field (fun _ : Degree P => 1) (atomBank a) x=∑ i,(a i).value x := by
  rw [← fieldCLM_apply]
  unfold atomBank
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [fieldCLM_apply,Atom.field_eq hN]

def flatCoefficients (P : ℕ) : ℕ →₀ ℝ :=
  Finsupp.indicator (Finset.Icc 2 P) (fun _ _ => 1)

theorem flatCoefficients_apply (P p : ℕ) :
    flatCoefficients P p = if p ∈ Finset.Icc 2 P then 1 else 0 := by
  simp [flatCoefficients,Finsupp.indicator_apply]

def flatMixture (P : ℕ) (hP : 2 ≤ P) : FiniteMixture where
  coeff := flatCoefficients P
  nonneg p := by rw [flatCoefficients_apply]; split_ifs <;> norm_num
  zero_below_two p hp := by
    rw [flatCoefficients_apply]
    split_ifs with h
    · have hh := (Finset.mem_Icc.mp h).1
      omega
    · rfl
  nonzero := by
    intro hz
    have h := congrArg (fun c : ℕ →₀ ℝ => c P) hz
    rw [flatCoefficients_apply] at h
    simp only [Finset.mem_Icc,hP,le_refl,and_self,ite_true,Finsupp.zero_apply] at h
    norm_num at h

theorem flatMixture_support (P : ℕ) (hP : 2 ≤ P) :
    (flatMixture P hP).coeff.support=Finset.Icc 2 P := by
  ext p
  change p ∈ (flatCoefficients P).support ↔ _
  rw [Finsupp.mem_support_iff,flatCoefficients_apply]
  split_ifs <;> simp_all

theorem flatMixture_maxDegree (P : ℕ) (hP : 2 ≤ P) :
    (flatMixture P hP).maxDegree=P := by
  apply le_antisymm
  · apply Finset.max'_le
    intro p hp
    rw [flatMixture_support] at hp
    exact (Finset.mem_Icc.mp hp).2
  · apply Finset.le_max'
    rw [flatMixture_support]
    exact Finset.mem_Icc.mpr ⟨hP,le_refl _⟩

theorem flatMixture_coefficient (P : ℕ) (hP : 2 ≤ P)
    (p : Degree (flatMixture P hP).maxDegree) :
    mixtureCoefficients (flatMixture P hP) p=1 := by
  change flatCoefficients P p.val.val=1
  rw [flatCoefficients_apply,ite_eq_left]
  apply Finset.mem_Icc.mpr
  refine ⟨p.property,?_⟩
  have hp := Nat.le_of_lt_succ p.val.isLt
  exact hp.trans_eq (flatMixture_maxDegree P hP)

theorem field_degree_transport {Q : ℕ} (h : Q=P) (J : Disorder N P) :
    field (fun _ : Degree Q => 1) (h.symm ▸ J)=field (fun _ : Degree P => 1) J := by
  subst Q
  rfl

/-- Every concrete finite atom family is an actual finite-mixture field.
The mixture is a deterministic full degree family; the coefficient bank
retains the exact prescribed products and amplitudes. -/
theorem atomBank_exists_physical_mixture (hN : 1 ≤ N) (hP : 2 ≤ P)
    {ι : Type*} [Fintype ι] (a : ι → Atom N P) :
    ∃ μ : FiniteMixture, ∃ J : Disorder N μ.maxDegree,
      fieldOfMixture μ J=fun x => ∑ i,(a i).value x := by
  let μ := flatMixture P hP
  have hm : μ.maxDegree=P := flatMixture_maxDegree P hP
  let J : Disorder N μ.maxDegree := hm.symm ▸ atomBank a
  refine ⟨μ,J,?_⟩
  have hc : mixtureCoefficients μ=fun _ => 1 := funext (flatMixture_coefficient P hP)
  have he : field (fun _ : Degree μ.maxDegree => 1) J =
      field (fun _ : Degree P => 1) (atomBank a) := by
    exact field_degree_transport hm (atomBank a)
  unfold fieldOfMixture
  rw [hc,he]
  funext x
  exact atomBank_field hN a x

def twoLinearAtom (u v : Vector N) (i j : ℕ) (hij : 2 ≤ i+j)
    (hP : i+j ≤ P) (b : ℝ) : Atom N P where
  degree := ⟨⟨i+j,Nat.lt_succ_of_le hP⟩,hij⟩
  coefficient := b
  factors := Fin.append (fun _ : Fin i => u) (fun _ : Fin j => v)

theorem twoLinearAtom_value (u v : Vector N) (i j : ℕ) (hij : 2 ≤ i+j)
    (hP : i+j ≤ P) (b : ℝ) (x : Vector N) :
    (twoLinearAtom u v i j hij hP b).value x=b*(inner ℝ u x)^i*(inner ℝ v x)^j := by
  unfold Atom.value twoLinearAtom
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left,Fin.append_right,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

/-- The actual original field expands in the coordinate product basis of
its original ordered coefficient tensors, with no symmetry quotient. -/
abbrev OriginalIndex (N : ℕ) (μ : FiniteMixture) :=
  Σ p : Degree μ.maxDegree, SphericalAging.FiniteModel.TensorIndex N p.val.val

def originalAtom (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (hP : μ.maxDegree ≤ P)
    (z : OriginalIndex N μ) : Atom N P where
  degree := ⟨⟨z.1.val.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ z.1.val.isLt).trans hP)⟩,z.1.property⟩
  coefficient := Real.sqrt (mixtureCoefficients μ z.1) *
    SphericalAging.FiniteModel.normalization N z.1.val.val * J z.1 z.2
  factors k := SphericalAging.HardSphereDynamics.basisVector (z.2 k)

theorem originalAtom_value (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (hP : μ.maxDegree ≤ P)
    (z : OriginalIndex N μ)
    (x : Vector N) :
    (originalAtom μ J hP z).value x=Real.sqrt (mixtureCoefficients μ z.1) *
      SphericalAging.FiniteModel.normalization N z.1.val.val * J z.1 z.2 *
      SphericalAging.FiniteModel.tensorMonomial x z.2 := by
  simp only [Atom.value,originalAtom,SphericalAging.HardSphereDynamics.basisVector,
    EuclideanSpace.inner_single_left,conj_trivial,one_mul,SphericalAging.FiniteModel.tensorMonomial]

theorem originalField_atom_sum (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (hP : μ.maxDegree ≤ P) (x : Vector N) :
    (∑ z : OriginalIndex N μ,
      (originalAtom μ J hP z).value x)=fieldOfMixture μ J x := by
  rw [Fintype.sum_sigma]
  simp only [originalAtom_value,fieldOfMixture,field,blockField,SphericalAging.FiniteModel.Hamiltonian]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  ring

end SlowEquilibration.ConditionedEntrance.TensorPolynomial
