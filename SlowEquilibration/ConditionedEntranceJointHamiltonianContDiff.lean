-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceJointKilling

/-! Joint C2 regularity of the literal source Hamiltonian, including
actual center value, radial jet and tangent gradient. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet PairConditionalDeterminantMoments
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem monomialSum_contDiff {ι : Type*} (s : Finset ι) (b : ι→ℝ) (n : ι→ℕ) :
    ContDiff ℝ ⊤ (monomialSum s b n) := by
  unfold monomialSum
  exact ContDiff.sum (fun i _ => contDiff_const.mul (contDiff_id.pow (n i)))

theorem valueTheta_contDiff (μ : FiniteMixture) (Q : ℝ) : ContDiff ℝ ⊤ (valueTheta μ Q) :=
  monomialSum_contDiff _ _ _

theorem radialTheta_contDiff (μ : FiniteMixture) (Q : ℝ) : ContDiff ℝ ⊤ (radialTheta μ Q) :=
  monomialSum_contDiff _ _ _

theorem tangentTheta_contDiff (μ : FiniteMixture) (Q : ℝ) : ContDiff ℝ ⊤ (tangentTheta μ Q) :=
  monomialSum_contDiff _ _ _

theorem radialJet_jointContDiff {P : ℕ} (c : Degree P→ℝ) :
    ContDiff ℝ ⊤ (fun z : Disorder N P×Vector N => jet c 1 z.2 (fun _ => z.2) z.1) := by
  have hd := source_param_fderiv_contDiff (fun (J : Disorder N P) (x : Vector N) => field c J x)
    (source_field_joint_contDiff c)
  simpa only [jet,iteratedFDeriv_one_apply] using hd.clm_apply contDiff_snd

theorem sourceSmoothCutoffField_jointContDiff (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (α : ℝ) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp z.1.1 z.1.2.1 z.1.2.2.1 z.1.2.2.2 α χ z.2) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let J : SourceParameters N μ × Vector N → Disorder N μ.maxDegree := fun z => z.1.1
  let u : SourceParameters N μ × Vector N → Vector N := fun z => z.1.2.1
  let h : SourceParameters N μ × Vector N → ℝ := fun z => z.1.2.2.1
  let k : SourceParameters N μ × Vector N → ℝ := fun z => z.1.2.2.2
  let G : SourceParameters N μ × Vector N → Vector N := fun z => surfaceGradient (field c (J z)) (u z)
  have hJ : ContDiff ℝ 2 J := contDiff_fst.fst
  have hu : ContDiff ℝ 2 u := contDiff_fst.snd.fst
  have hh : ContDiff ℝ 2 h := contDiff_fst.snd.snd.fst
  have hk : ContDiff ℝ 2 k := contDiff_fst.snd.snd.snd
  have hG := ((source_surfaceGradient_joint_contDiff c).of_le (by simp)).comp (hJ.prodMk hu)
  have hHq : ContDiff ℝ 2 (fun z => field c (J z) (u z)) :=
    ((source_field_joint_contDiff c).of_le (by simp)).comp (hJ.prodMk hu)
  have hKq := ((radialJet_jointContDiff c).of_le (by simp)).comp (hJ.prodMk hu)
  have hr : ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N => overlap z.2 (u z)) :=
    (contDiff_snd.inner ℝ hu).div_const _
  have hs : ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N => inner ℝ (G z) z.2) :=
    hG.inner ℝ contDiff_snd
  have hv : ContDiff ℝ 2 (valueTheta μ Q) := (valueTheta_contDiff μ Q).of_le (by simp)
  have hrad : ContDiff ℝ 2 (radialTheta μ Q) := (radialTheta_contDiff μ Q).of_le (by simp)
  have ht : ContDiff ℝ 2 (tangentTheta μ Q) := (tangentTheta_contDiff μ Q).of_le (by simp)
  have hcorr : ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N =>
      sourceRegressionCorrection μ Q hQ hnp (J z) (u z) (h z) (k z) z.2) := by
    unfold sourceRegressionCorrection regressionCorrection
    exact (((hv.comp hr).mul ((contDiff_const.mul hh).sub hHq)).add
      ((hrad.comp hr).mul ((contDiff_const.mul hk).sub hKq))).sub ((ht.comp hr).mul hs)
  have hbase : ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N => fieldOfMixture μ (J z) z.2) :=
    ((source_field_joint_contDiff (mixtureCoefficients μ)).of_le (by simp)).comp (hJ.prodMk contDiff_snd)
  have hfull : ContDiff ℝ 2 (fun z : SourceParameters N μ × Vector N => fieldOfMixture μ (J z) z.2+
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

theorem sourceJointHamiltonian_contDiff (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (sourceJointHamiltonian (N:=N) μ Q hQ hnp α χ) :=
  sourceSmoothCutoffField_jointContDiff μ Q hQ hnp α χ hχ

end SlowEquilibration.ConditionedEntrance
