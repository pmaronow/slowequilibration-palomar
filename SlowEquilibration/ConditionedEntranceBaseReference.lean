-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceReferenceFisher

/-! The source entropy reference is the original unconditioned mixture
Hamiltonian. Setting the two correction cutoffs to zero realizes it inside
the actual smooth physical construction, without changing its disorder. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging.HardSphereDynamics SphericalModel SphericalForm
open EntranceSmoothCutoffCalculus EntranceSmoothCutoffTensorApproximation
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

/-- The actual original mixture field, realized by zero correction cutoff. -/
def SourceData.baseData (D : SourceData N) : SourceData N :=
  {D with cutoff:=fun _ => 0,cutoff_smooth:=contDiff_const}

/-- The reference Hamiltonian is exactly the original disorder field;
its formula has no axis or conditioning marks. -/
theorem SourceData.baseData_hamiltonian (D : SourceData N) :
    D.baseData.hamiltonian=fieldOfMixture D.mixture D.disorder := by
  funext x
  simp only [SourceData.hamiltonian,SourceData.baseData,sourceSmoothCutoffField,
    smoothCutoffField,cutoffCorrection,zero_mul,add_zero]

/-- Source Fisher bound for the actual original unconditioned reference
process and original uniform start, at every positive physical rate. -/
theorem source_base_reference_fisher (D : SourceData N) (β : ℝ) (hβ : 0 ≤ β)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x,OnSphere x → |fieldOfMixture D.mixture D.disorder x| ≤ B)
    (θ : ℝ≥0) (hθ : 0 < θ) :
    ∃ u : sphericalSobolevGraph D.baseData.dimension_ge_one β D.baseData.hamiltonian
        D.baseData.hamiltonian_contDiff.continuous,
      sphericalEnergyL2Map D.baseData.dimension_ge_one β D.baseData.hamiltonian
          D.baseData.hamiltonian_contDiff.continuous u=
        referenceRate D.baseData β θ (referenceInitialVector D.baseData β) ∧
      0 ≤ sphericalFisher D.baseData.dimension_ge_one β D.baseData.hamiltonian
        D.baseData.hamiltonian_contDiff.continuous u ∧
      sphericalFisher D.baseData.dimension_ge_one β D.baseData.hamiltonian
          D.baseData.hamiltonian_contDiff.continuous u ≤ (θ : ℝ)*(2*Real.log 2+4*β*B) :=
  referenceRate_initial_fisher_bound D.baseData β hβ B hB0
    (by simpa only [SourceData.baseData_hamiltonian] using hB) θ hθ

end SlowEquilibration.ConditionedEntrance.SmoothKilled
