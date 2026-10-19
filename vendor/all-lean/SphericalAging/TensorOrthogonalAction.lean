module

public import SphericalAging.SphereTensorObservable
public import SphericalAging.OrthogonalGaussianDisclosure

public section

/-! The literal ordered tensor action of a vector orthogonal map. Its
isometry, Gaussian invariance and measurable evaluation are derived from
actual pure tensors, rather than supplied as adaptive frame assumptions. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.TensorOrthogonalAction
open Set MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics
open AdaptiveGradientDisclosure SphereTensorObservable
open scoped InnerProductSpace BigOperators

@[expose]  def rotatedFamily {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (I : TensorIndex N p) : TensorSpace N p :=
  pureTensor (fun k => O (basisVector (I k)))

 theorem rotatedFamily_orthonormal {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    Orthonormal ℝ (rotatedFamily (p:=p) O) := by
  classical
  rw [orthonormal_iff_ite]
  intro I J
  rw [rotatedFamily,rotatedFamily,pureTensor_inner]
  simp_rw [O.inner_map_map]
  by_cases h : I=J
  · subst J
    simp [basisVector]
  · rw [if_neg h]
    obtain ⟨k,hk⟩ : ∃k,I k≠J k := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [basisVector,EuclideanSpace.inner_single_left,EuclideanSpace.single_apply,hk,Ne.symm hk]

 theorem exists_rotatedBasis {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    ∃b : OrthonormalBasis (TensorIndex N p) ℝ (TensorSpace N p),∀I,b I=rotatedFamily O I := by
  obtain ⟨b,hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℝ (TensorSpace N p)=Fintype.card (TensorIndex N p))
    ((rotatedFamily_orthonormal (p:=p) O).comp (fun I : (univ:Set (TensorIndex N p)) => (I:TensorIndex N p))
      Subtype.val_injective)
  exact ⟨b,fun I => hb I (mem_univ I)⟩

@[expose]  def rotatedBasis {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    OrthonormalBasis (TensorIndex N p) ℝ (TensorSpace N p) := (exists_rotatedBasis (p:=p) O).choose

 theorem rotatedBasis_apply {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (I : TensorIndex N p) :
    rotatedBasis O I=rotatedFamily O I := (exists_rotatedBasis O).choose_spec I

@[expose]  def action {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) : TensorSpace N p≃ₗᵢ[ℝ]TensorSpace N p :=
  (EuclideanSpace.basisFun (TensorIndex N p) ℝ).equiv (rotatedBasis O) (Equiv.refl _)

 theorem action_basis {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (I : TensorIndex N p) :
    action O (EuclideanSpace.single I 1)=rotatedFamily O I := by
  rw [←EuclideanSpace.basisFun_apply]
  exact ((EuclideanSpace.basisFun (TensorIndex N p) ℝ).equiv_apply_basis (rotatedBasis O) (Equiv.refl _) I).trans
    (rotatedBasis_apply O I)

 theorem action_apply {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (J : TensorSpace N p) :
    action O J=∑I : TensorIndex N p,J I • rotatedFamily O I := by
  change (EuclideanSpace.basisFun (TensorIndex N p) ℝ).equiv (rotatedBasis O) (Equiv.refl _) J=_
  rw [OrthonormalBasis.equiv_apply_euclideanSpace]
  simp_rw [rotatedBasis_apply]

 theorem action_pureTensor {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) (v : Fin p→Vector N) :
    action O (pureTensor v)=pureTensor (fun k => O (v k)) := by
  apply (rotatedBasis O).repr.injective
  ext I
  have hL : (rotatedBasis O).repr (action O (pureTensor v)) I=(pureTensor v) I := by
    rw [OrthonormalBasis.repr_apply_apply,rotatedBasis_apply,←action_basis,(action O).inner_map_map,
      EuclideanSpace.inner_single_left]
    simp
  have hR : (rotatedBasis O).repr (pureTensor (fun k => O (v k))) I=(pureTensor v) I := by
    rw [OrthonormalBasis.repr_apply_apply,rotatedBasis_apply,rotatedFamily,pureTensor_inner]
    simp only [O.inner_map_map,basisVector,EuclideanSpace.inner_single_left,one_mul]
    simp [pureTensor]
  exact hL.trans hR.symm

 theorem action_gaussian {N p : ℕ} (O : Vector N≃ₗᵢ[ℝ]Vector N) :
    MeasurePreserving (action (p:=p) O) (stdGaussian (TensorSpace N p)) (stdGaussian (TensorSpace N p)) :=
  ⟨(action O).continuous.measurable,stdGaussian_map (action O)⟩

 theorem action_measurable {N p : ℕ} {S : Type*} [MeasurableSpace S]
    (O : S→Vector N≃ₗᵢ[ℝ]Vector N)
    (hO : Measurable (fun z : S×Vector N => O z.1 z.2)) :
    Measurable (fun z : S×TensorSpace N p => action (O z.1) z.2) := by
  classical
  have hf : ∀I : TensorIndex N p,Measurable (fun z : S×TensorSpace N p => rotatedFamily (O z.1) I) := by
    intro I
    have hv : Measurable (fun z : S×TensorSpace N p => fun k : Fin p => O z.1 (basisVector (I k))) :=
      measurable_pi_iff.mpr (fun k => hO.comp (measurable_fst.prodMk measurable_const))
    have hh := ((pureForm N p).contDiff (n:=⊤)).continuous.measurable.comp hv
    have he : (pureForm N p)∘(fun z : S×TensorSpace N p => fun k : Fin p => O z.1 (basisVector (I k)))=
        (fun z : S×TensorSpace N p => rotatedFamily (O z.1) I) := by
      funext z
      exact pureForm_apply _
    rw [he] at hh
    exact hh
  have hh : Measurable (fun z : S×TensorSpace N p => ∑I : TensorIndex N p,z.2 I • rotatedFamily (O z.1) I) := by
    apply Finset.measurable_sum
    intro I _
    have hi : Measurable (fun z : S×TensorSpace N p => z.2 I) :=
      (measurable_pi_apply I).comp ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_snd)
    exact hi.smul (hf I)
  simpa only [action_apply] using hh

end SphericalAging.TensorOrthogonalAction
