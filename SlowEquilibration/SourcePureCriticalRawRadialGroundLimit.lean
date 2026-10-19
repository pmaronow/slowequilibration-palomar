-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalRadialGroundLimit

/-! The literal source §11.14 energy window carries no auxiliary clip: its
fixed radial-mark interval enforces that clip pathwise for pure fields. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set Filter MeasureTheory SphericalModel SphericalGaussianJet
open TwoAtomStationarity SphericalTAPCertificate
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal Topology
set_option autoImplicit false

/-- The original normalized energy window before any auxiliary value cut. -/
def sourcePureCenteredRawNormalizedWindow
    (n : ℕ) (m : ℕ → ℝ) (L R : ℝ) : Set ℝ :=
  (fun b : ℝ => ((n+3 : ℕ) : ℝ)*b) ⁻¹'
    Icc (m (n+1)+L) (m (n+1)+R)

/-- In the pure field, a fixed open radial interval clips the value mark
exactly to the source contact box. This is pointwise in the disorder and
holds for every dimension. -/
theorem sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ : ℝ) (m : ℕ → ℝ) (L R : ℝ)
    (J : Disorder (n+3) (FiniteMixture.pure p hp a ha).maxDegree) :
    let c := centerCoefficients (mixtureCoefficients (FiniteMixture.pure p hp a ha)) Q
    let V := sourcePureCenteredRawNormalizedWindow n m L R
    let U := Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))
    actualScoreWindowCount (n+2) c
      {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
      (fun _ _ => 1) J =
    actualValueWindowCount (n+2) c
      (sourcePureCenteredNormalizedWindow n m E δ L R)
      (fun _ _ => 1) J := by
  classical
  dsimp only
  rw [actual_pure_scoreWindowCount_eq_valueWindowCount (n+2) p hp a ha Q]
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hset : pureScoreWindow p
      {b : EuclideanSpace ℝ (Fin 2) |
        b 0 ∈ sourcePureCenteredRawNormalizedWindow n m L R ∧
        b 1 ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))} =
      sourcePureCenteredNormalizedWindow n m E δ L R := by
    ext b
    simp only [pureScoreWindow,pureScoreLine,Set.mem_preimage,Set.mem_ofPred_eq,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    change (((n+3 : ℕ) : ℝ)*b ∈ Icc (m (n+1)+L) (m (n+1)+R) ∧
      (p : ℝ)*b ∈ Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ))) ↔
      (((n+3 : ℕ) : ℝ)*b ∈ Icc (m (n+1)+L) (m (n+1)+R) ∧
        ((n+3 : ℕ) : ℝ)*b ∈
          Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)))
    have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
    constructor
    · intro hb
      exact ⟨hb.1,
        ⟨mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.1 hp0.le) hN,
          mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.2 hp0.le) hN⟩⟩
    · intro hb
      exact ⟨hb.1,
        ⟨mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.1 hN.le) hp0,
          mul_lt_mul_of_pos_left (lt_of_mul_lt_mul_left hb.2.2 hN.le) hp0⟩⟩
  rw [hset]

/-- Source §11.14 for a proper-pure original field with the literal raw
energy window and one fixed open radial interval selected before all
window widths. The critical count is an ordinary unsigned set count. -/
theorem source_pure_actual_raw_score_critical_joint_ground_limit
    (p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {β x Q : ℝ} (h : Certificate (FiniteMixture.pure p hp a ha) β x Q) :
    let μ := FiniteMixture.pure p hp a ha
    let E := markE μ β x Q
    ∃ m : ℕ → ℝ, ∃ δ : ℝ, ∃ U : Set ℝ,
      0 < δ ∧ U = Ioo ((p : ℝ)*(E-δ)) ((p : ℝ)*(E+δ)) ∧
      IsOpen U ∧ (p : ℝ)*E ∈ U ∧
      (∀ L : ℝ, 0 < L → ∃ B : ℝ, ∀ n : ℕ,
        let V := sourcePureCenteredRawNormalizedWindow n m (-L) L
        let K := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V ∧ b 1 ∈ U}
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) < ⊤ ∧
        (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q) K
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree).toReal ≤ B) ∧
      ∀ z : ℝ, 0 < z → ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀,
        let V n := sourcePureCenteredRawNormalizedWindow n m (-L) L
        let K n := {b : EuclideanSpace ℝ (Fin 2) | b 0 ∈ V n ∧ b 1 ∈ U}
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
  refine ⟨m,δ,U,hδ,rfl,isOpen_Ioo,hE,?_,?_⟩
  · intro L hL
    obtain ⟨B,hB⟩ := hCount L hL
    refine ⟨B,?_⟩
    intro n
    have heq : (∫⁻ J, actualScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          {b : EuclideanSpace ℝ (Fin 2) |
            b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧ b 1 ∈ U}
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) =
        (∫⁻ J, actualValueWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (sourcePureCenteredNormalizedWindow n m E δ (-L) L)
          (fun _ _ => 1) J ∂disorderLaw (n+3) μ.maxDegree) := by
      apply lintegral_congr
      intro J
      exact sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
        n p hp a ha Q E δ m (-L) L J
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
              b 0 ∈ sourcePureCenteredRawNormalizedWindow n m (-L) L ∧ b 1 ∈ U}
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
      have hpoint := sourcePureCenteredRawScoreWindow_eq_clippedValueWindow
        n p hp a ha Q E δ m (-L) L J
      dsimp only [μ,E,U] at hpoint ⊢
      simp only [Set.mem_ofPred_eq,hpoint]
    dsimp only [μ,E,U] at hfun ⊢
    simpa only [hfun] using hValue

end SlowEquilibration.SphericalMarkedWindows
