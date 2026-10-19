-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalRadialWindowBridge
public import SlowEquilibration.SourcePureRetainedJointGroundLimit

/-! The source §11.14 critical count with a fixed open radial-mark interval,
for the original proper-pure Gaussian tensor field. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false

/-- Any radial set containing the Euler image of the energy window gives
exactly the same proper-pure critical count, pathwise. -/
theorem pure_actualScoreWindowCount_of_radial_cover
    (N p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ)
    (I U : Set ℝ) (hIU : ∀ b ∈ I, (p : ℝ)*b ∈ U)
    (J : Disorder (N+1) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    actualScoreWindowCount N c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ I ∧ b 1 ∈ U}
      (fun _ _ => 1) J =
    actualValueWindowCount N c I (fun _ _ => 1) J := by
  classical
  dsimp only
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount N p hp a ha Q]
  have hset : pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ I ∧ b 1 ∈ U} = I := by
    ext b
    change (b ∈ I ∧ (p : ℝ)*b ∈ U) ↔ b ∈ I
    exact ⟨And.left, fun hb => ⟨hb,hIU b hb⟩⟩
  rw [hset]

/-- The centered, clipped value window always has its radial score inside
the same open Euler interval, including in small dimensions. -/
theorem sourcePureCenteredScoreWindow_eq_valueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (L R : ℝ)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    let I := sourcePureCenteredNormalizedWindow n m E δ L R
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    actualScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ I ∧ b 1 ∈ U}
      (fun _ _ => 1) J =
    actualValueWindowCount (n+2) c I (fun _ _ => 1) J := by
  dsimp only
  apply pure_actualScoreWindowCount_of_radial_cover (n+2) p hp a ha Q
  intro b hb
  have hbox := hb.2
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hleft : E-δ < b := lt_of_mul_lt_mul_left hbox.1 hN.le
  have hright : b < E+δ := lt_of_mul_lt_mul_left hbox.2 hN.le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  exact ⟨mul_lt_mul_of_pos_left hleft hp0,
    mul_lt_mul_of_pos_left hright hp0⟩

/-- The printed radial mark may be one fixed open interval before choosing
the centered window width. The endpoint is the original-field score count. -/
theorem source_pure_actual_score_critical_joint_ground_limit
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∃ m : ℕ → ℝ, ∃ δ : ℝ, ∃ U : Set ℝ,
      0 < δ ∧ IsOpen U ∧ (p : ℝ)*E ∈ U ∧
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        let I := sourcePureCenteredNormalizedWindow n m E δ (-L) L
        let K := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ I ∧ b 1 ∈ U}
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B) ∧
      ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
        let I n := sourcePureCenteredNormalizedWindow n m E δ (-L) L
        let K n := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ I n ∧ b 1 ∈ U}
        Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | |sourceSphereMaximum (n+1) μ Q J-m (n+1)| > L}) Filter.atTop ≤ z ∧
        1-z ≤ Filter.liminf (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | actualScoreWindowCount (n+2)
              (centerCoefficients (mixtureCoefficients μ) Q) (K n)
              (fun _ _ => 1) J ≠ 0 ∧
              sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) Filter.atTop := by
  dsimp only
  let μ := FiniteMixture.pure p hp a ha
  let E := markE μ β x Q
  obtain ⟨m,C,η,ε,δ,hδ,hCount,hJoint⟩ :=
    source_pure_actual_retained_joint_ground_limit p hp a ha h
  let U : Set ℝ := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hE : (p : ℝ)*E ∈ U := by
    dsimp [U]
    exact ⟨mul_lt_mul_of_pos_left (by linarith) hp0,
      mul_lt_mul_of_pos_left (by linarith) hp0⟩
  refine ⟨m,δ,U,hδ,isOpen_Ioo,hE,?_,?_⟩
  · intro L hL
    obtain ⟨B,hB⟩ := hCount L hL
    refine ⟨B,?_⟩
    intro n
    have heq : (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          {b : EuclideanSpace ℝ (Fin 2) |
            b 0 ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L ∧ b 1 ∈ U}
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) =
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) := by
      apply lintegral_congr
      intro J
      exact sourcePureCenteredScoreWindow_eq_valueWindow n p hp a ha Q E δ m (-L) L J
    dsimp only [U]
    constructor
    · rw [heq]
      exact (hB n).1
    · rw [heq]
      simpa only [sourceUnfilteredValueWindowMean] using (hB n).2
  · intro z hz
    obtain ⟨L₀,hL₀,hForall⟩ := hJoint z hz
    refine ⟨L₀,hL₀,?_⟩
    intro L hL
    obtain ⟨hDev,hRet,hValue⟩ := hForall L hL
    refine ⟨hDev,?_⟩
    have hfun : (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | actualScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            {b : EuclideanSpace ℝ (Fin 2) |
              b 0 ∈ sourcePureCenteredNormalizedWindow n m E δ (-L) L ∧ b 1 ∈ U}
            (fun _ _ => 1) J ≠ 0 ∧
            sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) =
        (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
          {J | actualValueWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
            (fun _ _ => 1) J ≠ 0 ∧
            sourceSphereMaximum (n+1) μ Q J < m (n+1)+L}) := by
      funext n
      congr 1
      ext J
      have hpoint :=
        sourcePureCenteredScoreWindow_eq_valueWindow n p hp a ha Q E δ m (-L) L J
      dsimp only [μ,E,U] at hpoint
      dsimp only [μ,E,U]
      simp only [Set.mem_ofPred_eq,hpoint]
    dsimp only [μ,E,U] at hfun ⊢
    simpa only [hfun] using hValue

end SlowEquilibration.SphericalMarkedWindows
