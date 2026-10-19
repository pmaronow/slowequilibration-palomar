-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureSmoothCutoff
public import SlowEquilibration.SphericalJointSpatialGradient

/-! Joint C2 regularity of the proper-pure source and joint C1 regularity
of its literal spatial gradient. The radial mark is unused because the
proper scalar value posterior has only one independent scalar mark. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet PairConditionalDeterminantMoments
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

def pureSourceJointHamiltonian (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    (Q α : ℝ) (χ : ℝ→ℝ) :
    SourceParameters N (FiniteMixture.pure p hp c hc)×Vector N→ℝ :=
  fun z => pureSourceSmoothCutoffField p hp c hc Q z.1.1 z.1.2.1 z.1.2.2.1 α χ z.2

theorem attachedPureCorrection_jointContDiff (μ : FiniteMixture) (p : ℕ) (Q : ℝ) :
    ContDiff ℝ ⊤ (fun z : SourceParameters N μ×Vector N =>
      pureRegressionCorrection p Q z.1.2.1
        (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) z.1.1) z.1.2.1)
        (field (centerCoefficients (mixtureCoefficients μ) Q) z.1.1 z.1.2.1) z.1.2.2.1 z.2) := by
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  have hJu : ContDiff ℝ ⊤ (fun z : SourceParameters N μ×Vector N => (z.1.1,z.1.2.1)) :=
    contDiff_fst.fst.prodMk contDiff_fst.snd.fst
  have hG := (source_surfaceGradient_joint_contDiff cQ).comp hJu
  have hHq := (source_field_joint_contDiff cQ).comp hJu
  have hr : ContDiff ℝ ⊤ (fun z : SourceParameters N μ×Vector N => overlap z.2 z.1.2.1) :=
    (contDiff_snd.inner ℝ contDiff_fst.snd.fst).div_const _
  have hs : ContDiff ℝ ⊤ (fun z : SourceParameters N μ×Vector N =>
      inner ℝ (surfaceGradient (field cQ z.1.1) z.1.2.1) z.2) := hG.inner ℝ contDiff_snd
  unfold pureRegressionCorrection
  exact contDiff_const.mul ((((contDiff_const.mul contDiff_fst.snd.snd.fst).sub hHq).mul
    (hr.pow p)).sub ((hr.pow (p-1)).mul hs))

def scalarSourceCutoff (χ : ℝ→ℝ) (z : ℝ×(ℝ×(ℝ×ℝ))) : ℝ :=
  z.1+χ z.2.1*χ z.2.2.1*z.2.2.2

theorem scalarSourceCutoff_contDiff (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (scalarSourceCutoff χ) :=
  contDiff_fst.add (((hχ.comp contDiff_snd.fst).mul (hχ.comp contDiff_snd.snd.fst)).mul
    contDiff_snd.snd.snd)

theorem attachedPureSmoothCutoff_jointContDiff (μ : FiniteMixture) (p : ℕ) (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (fun z : SourceParameters N μ×Vector N =>
      fieldOfMixture μ z.1.1 z.2+
        χ (overlap z.2 z.1.2.1/α)*
          χ (inner ℝ (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) z.1.1) z.1.2.1) z.2/((N : ℝ)*α))*
            pureRegressionCorrection p Q z.1.2.1
              (surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) z.1.1) z.1.2.1)
              (field (centerCoefficients (mixtureCoefficients μ) Q) z.1.1 z.1.2.1) z.1.2.2.1 z.2) := by
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let J : SourceParameters N μ×Vector N→Disorder N μ.maxDegree := fun z => z.1.1
  let u : SourceParameters N μ×Vector N→Vector N := fun z => z.1.2.1
  let e : SourceParameters N μ×Vector N→ℝ := fun z => z.1.2.2.1
  let G : SourceParameters N μ×Vector N→Vector N := fun z => surfaceGradient (field cQ (J z)) (u z)
  have hJ : ContDiff ℝ 2 J := contDiff_fst.fst
  have hu : ContDiff ℝ 2 u := contDiff_fst.snd.fst
  have hG := ((source_surfaceGradient_joint_contDiff cQ).of_le (by simp)).comp (hJ.prodMk hu)
  have hr : ContDiff ℝ 2 (fun z : SourceParameters N μ×Vector N => overlap z.2 (u z)) :=
    (contDiff_snd.inner ℝ hu).div_const _
  have hs : ContDiff ℝ 2 (fun z : SourceParameters N μ×Vector N => inner ℝ (G z) z.2) :=
    hG.inner ℝ contDiff_snd
  have hcorr : ContDiff ℝ 2 (fun z : SourceParameters N μ×Vector N =>
      pureRegressionCorrection p Q (u z) (G z) (field cQ (J z) (u z)) (e z) z.2) :=
    (attachedPureCorrection_jointContDiff μ p Q).of_le (by simp)
  have hbase : ContDiff ℝ 2 (fun z : SourceParameters N μ×Vector N => fieldOfMixture μ (J z) z.2) :=
    ((source_field_joint_contDiff (mixtureCoefficients μ)).of_le (by simp)).comp (hJ.prodMk contDiff_snd)
  have hm := hbase.prodMk ((hr.div_const α).prodMk ((hs.div_const ((N : ℝ)*α)).prodMk hcorr))
  have ht := (scalarSourceCutoff_contDiff χ hχ).comp hm
  simpa only [scalarSourceCutoff,Function.comp_def,J,u,e,G,cQ] using ht

theorem pureSourceJointHamiltonian_contDiff (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 2 (pureSourceJointHamiltonian (N:=N) p hp c hc Q α χ) := by
  unfold pureSourceJointHamiltonian pureSourceSmoothCutoffField pureSourceRegressionCorrection
  exact attachedPureSmoothCutoff_jointContDiff (N:=N) (FiniteMixture.pure p hp c hc) p Q α χ hχ

theorem pureSourceJointSpatialGradient_contDiff (p : ℕ) (hp : 2≤p) (c : ℝ) (hc : 0<c)
    (Q α : ℝ) (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ) :
    ContDiff ℝ 1 (jointSpatialGradient (pureSourceJointHamiltonian (N:=N) p hp c hc Q α χ)) :=
  jointSpatialGradient_contDiff _ (pureSourceJointHamiltonian_contDiff p hp c hc Q α χ hχ)

end SlowEquilibration.ConditionedEntrance
