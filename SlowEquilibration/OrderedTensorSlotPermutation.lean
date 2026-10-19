-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OrderedTensorTracePhysicalEnvelope

/-! All ordered-slot permutations preserve the actual original iid tensor
law. Thus every fixed pairing of contraction slots has the genuine trace
bank and the proved physical envelope, with no symmetrized-tensor law
substitution. -/

@[expose] public section
namespace SlowEquilibration.OrderedTensorTraceGaussianBank
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalAging.FiniteModel
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def tensorSlotIndexEquiv {N p : ℕ} (σ : Equiv.Perm (Fin p)) :
    Equiv.Perm (TensorIndex N p) := Equiv.piCongrLeft' (fun _ : Fin p => Fin N) σ

def permutedTensor {N p : ℕ} (σ : Equiv.Perm (Fin p)) :
    SphericalAging.FiniteModel.Disorder N p ≃ᵐ SphericalAging.FiniteModel.Disorder N p :=
  MeasurableEquiv.piCongrLeft (fun _ : TensorIndex N p => ℝ) (tensorSlotIndexEquiv σ)

/-- Literal reordering of original tensor slots. -/
theorem permutedTensor_apply {N p : ℕ} (σ : Equiv.Perm (Fin p))
    (J : SphericalAging.FiniteModel.Disorder N p) (I : TensorIndex N p) :
    permutedTensor σ J I=J (I ∘ σ) := by
  classical
  change Equiv.piCongrLeft (fun _ : TensorIndex N p => ℝ) (tensorSlotIndexEquiv σ) J I=_
  rw [Equiv.piCongrLeft_apply]
  simp only [eq_rec_constant,tensorSlotIndexEquiv,Equiv.piCongrLeft'_symm]
  rfl

/-- Actual ordered product disorder is invariant under every slot permutation. -/
theorem permutedTensor_measurePreserving {N p : ℕ} (σ : Equiv.Perm (Fin p)) :
    MeasurePreserving (permutedTensor (N := N) σ)
      (SphericalAging.FiniteModel.disorderLaw N p) (SphericalAging.FiniteModel.disorderLaw N p) :=
  measurePreserving_piCongrLeft (fun _ => gaussianReal 0 1) (tensorSlotIndexEquiv σ)

def permutedTracedHamiltonian (N q j : ℕ) (σ : Equiv.Perm (Fin (q+j+j)))
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (x : Vector N) : ℝ :=
  tracedHamiltonian N q j (permutedTensor σ J) x

def permutedTraceEnvelope (N q j : ℕ) (σ : Equiv.Perm (Fin (q+j+j)))
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) : ℝ :=
  tracedPhysicalEnvelope N q j (permutedTensor σ J)

/-- Every ordered pairing retains the same literal Gaussian trace-bank law. -/
theorem actual_permutedTensorTrace_hasLaw {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (σ : Equiv.Perm (Fin (q+j+j))) :
    HasLaw (fun J => rawOrderedTensorTrace N q j (permutedTensor σ J))
      (SphericalAging.FiniteModel.disorderLaw N q)
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) :=
  (actual_rawOrderedTensorTrace_hasLaw hN q j).fun_comp
    (permutedTensor_measurePreserving σ).hasLaw

theorem permutedTraceEnvelope_integrable {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (σ : Equiv.Perm (Fin (q+j+j))) :
    Integrable (permutedTraceEnvelope N q j σ)
      (SphericalAging.FiniteModel.disorderLaw N (q+j+j)) :=
  (permutedTensor_measurePreserving σ).hasLaw.integrable_comp
    (tracedPhysicalEnvelope_integrable hN q j)

theorem permutedTracedHamiltonian_abs_le {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (σ : Equiv.Perm (Fin (q+j+j)))
    (J : SphericalAging.FiniteModel.Disorder N (q+j+j)) (x : Vector N)
    (hx : ‖x‖ ≤ Real.sqrt N) :
    |permutedTracedHamiltonian N q j σ J x| ≤ permutedTraceEnvelope N q j σ J :=
  tracedHamiltonian_abs_le_envelope hN q j (permutedTensor σ J) x hx

/-- Uniform expected source-scale envelope for any ordered pairing of slots. -/
theorem expected_permutedTraceEnvelope_le {N : ℕ} (hN : 0 < N) (q j : ℕ)
    (hp : 1 ≤ q+j+j) (σ : Equiv.Perm (Fin (q+j+j))) :
    (∫ J,permutedTraceEnvelope N q j σ J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j)) ≤
      4*Real.sqrt (q+1)*(N : ℝ)^(1-(j : ℝ)/2) := by
  have hh := (permutedTensor_measurePreserving σ).hasLaw.integral_comp
    (tracedPhysicalEnvelope_integrable hN q j).aestronglyMeasurable
  change (∫ J,permutedTraceEnvelope N q j σ J ∂SphericalAging.FiniteModel.disorderLaw N (q+j+j))=_ at hh
  rw [hh]
  exact expected_tracedPhysicalEnvelope_le_all hN q j hp

end
end SlowEquilibration.OrderedTensorTraceGaussianBank
