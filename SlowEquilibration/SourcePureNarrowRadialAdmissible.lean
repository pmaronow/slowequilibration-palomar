-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureRetainedJointGroundLimitNarrowRadial
public import SlowEquilibration.SourcePhysicalPurePairSelectionFailureProbability

/-! The narrowed proper-pure radial mark interval has closure inside the
fixed source §11 admissible interval `[2√b+κ,K₀+1]`. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set SphericalModel SphericalGaussianJet TwoAtomStationarity SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false

theorem source_pure_narrow_radial_interval_admissible
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q δ : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q)
    (hδ : 0 < δ)
    (hLeft :
      2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q)+
        (markK (FiniteMixture.pure p hp a ha) β Q-
          2*Real.sqrt (Q^2*(FiniteMixture.pure p hp a ha).xi2 Q))/2 ≤
        (p : ℝ)*(markE (FiniteMixture.pure p hp a ha) β x Q-δ))
    (hpδ : (p : ℝ)*δ < 1) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    let K₀ := markK μ β Q
    let κ := (K₀-2*Real.sqrt (Q^2*μ.xi2 Q))/2
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    IsOpen U ∧ K₀ ∈ U ∧
      closure U ⊆ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+κ) (K₀+1) := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  let K₀ := markK μ β Q
  let κ := (K₀-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hK : K₀ = (p : ℝ)*E := source_pure_markK_eq_degree_mul_markE p hp a ha h
  have hBand : (p : ℝ)*(E-δ) < (p : ℝ)*(E+δ) :=
    mul_lt_mul_of_pos_left (by linarith) hp0
  refine ⟨isOpen_Ioo,?_,?_⟩
  · change K₀ ∈ U
    rw [hK]
    exact ⟨mul_lt_mul_of_pos_left (by linarith) hp0,
      mul_lt_mul_of_pos_left (by linarith) hp0⟩
  · change closure U ⊆ Icc (2*Real.sqrt (Q^2*μ.xi2 Q)+κ) (K₀+1)
    rw [show closure U = Icc ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) from
      closure_Ioo hBand.ne]
    intro k hk
    constructor
    · exact hLeft.trans hk.1
    · have hu : (p : ℝ)*(E+δ) < K₀+1 := by
        rw [hK]
        nlinarith [hpδ]
      exact hk.2.trans hu.le

end SlowEquilibration.PairConditionalDeterminantMoments
