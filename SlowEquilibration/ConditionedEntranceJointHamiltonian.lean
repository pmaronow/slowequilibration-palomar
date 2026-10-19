-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothStationarity
public import SlowEquilibration.ConditionedEntranceJointJets

/-! Joint disorder/axis/mark continuity of the literal smooth entrance
Hamiltonian, with the actual center field gradient and radial jet. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet
open PairConditionalDeterminantMoments
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

abbrev SourceParameters (N : ℕ) (μ : FiniteMixture) :=
  Disorder N μ.maxDegree × (Vector N × (ℝ × ℝ))

theorem sourceSmoothCutoffField_jointContinuous (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ → ℝ) (hχ : Continuous χ) :
    Continuous (fun z : SourceParameters N μ × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 α χ z.2) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let J : SourceParameters N μ × Vector N → Disorder N μ.maxDegree := fun z => z.1.1
  let u : SourceParameters N μ × Vector N → Vector N := fun z => z.1.2.1
  let h : SourceParameters N μ × Vector N → ℝ := fun z => z.1.2.2.1
  let k : SourceParameters N μ × Vector N → ℝ := fun z => z.1.2.2.2
  let G : SourceParameters N μ × Vector N → Vector N := fun z => surfaceGradient (field c (J z)) (u z)
  have hJ : Continuous J := continuous_fst.fst
  have hu : Continuous u := continuous_fst.snd.fst
  have hh : Continuous h := continuous_fst.snd.snd.fst
  have hk : Continuous k := continuous_fst.snd.snd.snd
  have hG := (source_surfaceGradient_joint_contDiff c).continuous.comp (hJ.prodMk hu)
  have hHq : Continuous (fun z => field c (J z) (u z)) := (field_jointContinuous c).comp (hJ.prodMk hu)
  have hKq := (radialJet_jointContinuous c).comp (hJ.prodMk hu)
  have hr : Continuous (fun z : SourceParameters N μ × Vector N => overlap z.2 (u z)) :=
    (continuous_snd.inner hu).div_const _
  have hs : Continuous (fun z : SourceParameters N μ × Vector N => inner ℝ (G z) z.2) :=
    hG.inner continuous_snd
  have hv := valueTheta_continuous μ Q
  have hrad := radialTheta_continuous μ Q
  have ht := tangentTheta_continuous μ Q
  have hcorr : Continuous (fun z : SourceParameters N μ × Vector N =>
      sourceRegressionCorrection μ Q hQ hnp (J z) (u z) (h z) (k z) z.2) := by
    unfold sourceRegressionCorrection regressionCorrection
    exact (((hv.comp hr).mul ((hh.const_mul (N : ℝ)).sub hHq)).add
      ((hrad.comp hr).mul ((hk.const_mul (N : ℝ)).sub hKq))).sub ((ht.comp hr).mul hs)
  have hbase : Continuous (fun z : SourceParameters N μ × Vector N => fieldOfMixture μ (J z) z.2) :=
    (field_jointContinuous (mixtureCoefficients μ)).comp (hJ.prodMk continuous_snd)
  have hfull : Continuous (fun z : SourceParameters N μ × Vector N => fieldOfMixture μ (J z) z.2+
      χ (overlap z.2 (u z)/α)*χ (inner ℝ (G z) z.2/((N : ℝ)*α))*
        sourceRegressionCorrection μ Q hQ hnp (J z) (u z) (h z) (k z) z.2) :=
    hbase.add (((hχ.comp (hr.div_const α)).mul (hχ.comp (hs.div_const _))).mul hcorr)
  have he : (fun z : SourceParameters N μ × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 α χ z.2)=
      (fun z : SourceParameters N μ × Vector N => fieldOfMixture μ (J z) z.2+
        χ (overlap z.2 (u z)/α)*χ (inner ℝ (G z) z.2/((N : ℝ)*α))*
          sourceRegressionCorrection μ Q hQ hnp (J z) (u z) (h z) (k z) z.2) :=
    funext (fun z => sourceSmoothCutoffField_eq μ Q hQ hnp z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 α χ z.2)
  rw [he]
  exact hfull

end SlowEquilibration.ConditionedEntrance
