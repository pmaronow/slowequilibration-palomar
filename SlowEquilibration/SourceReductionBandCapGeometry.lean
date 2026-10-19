-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionEvolvedCapMass

/-! A source critical-center band lies inside its center cap when the cap
threshold is strictly below the lower edge of the latitude band. -/

@[expose] public section
namespace SlowEquilibration.SourceReductionBandCapGeometry
noncomputable section
open Set SphericalModel SphericalRotationCovariance
open SourceReductionClosedBandGraph SourceReductionPointCapMass
open SourceReductionEvolvedCapMass
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 700000

variable {N : ℕ}

/-- Literal source band union in the ambient physical sphere is contained
in the same centers' two-sided cap union. -/
theorem physicalSphereBandUnion_subset_pointCapUnion
    (μ : FiniteMixture) (Q m M b a : ℝ) (U : Set ℝ)
    (J : Disorder N μ.maxDegree)
    (ha : a < Real.sqrt Q - b) :
    {x : Vector N | (J,x) ∈ physicalSphereBandUnionGraph μ Q m M b U} ⊆
      ambientPointCapUnion μ Q m M a U J := by
  intro x hx
  have hxband : (J,x) ∈ bandUnionGraph μ Q m M b U := hx.1
  have hxsphere : OnSphere x := (onSphere_iff_norm_sq x).mpr hx.2
  let X : PhysicalSphere N := ⟨x,hxsphere⟩
  obtain ⟨u,hu,hb⟩ := hxband
  have husphere : OnSphere u := by
    unfold windowCenterGraph at hu
    exact (onSphere_iff_norm_sq u).mpr hu.1.1.1
  let V : PhysicalSphere N := ⟨u,husphere⟩
  have hlat : Real.sqrt Q - b ≤ overlap x u := by
    have habs : |overlap x u - Real.sqrt Q| ≤ b := hb
    have := (abs_le.mp habs).1
    linarith
  have hcap : a ≤ |overlap x u| :=
    le_trans (le_of_lt ha) (le_trans hlat (le_abs_self _))
  change ∃ y : PhysicalSphere N,
    (J,y) ∈ pointCapUnionGraph μ Q m M a U ∧ y.1 = x
  refine ⟨X,?_,rfl⟩
  exact ⟨V,hu,hcap⟩

end
end SlowEquilibration.SourceReductionBandCapGeometry
