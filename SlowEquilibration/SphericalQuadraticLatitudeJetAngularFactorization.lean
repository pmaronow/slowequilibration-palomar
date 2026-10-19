-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetBankDeterminantCauchy
public import SlowEquilibration.SphericalQuadraticLatitudeJetPalmFactorization
public import SlowEquilibration.SphericalTAPMixedPalmLatitudeMeasurable
public import SlowEquilibration.PositiveAngularFactorization

@[expose] public section

/-! Angular Fubini for the determinant-weighted original latitude field.
The scalar residual moment and one-point integrability are stated as inputs
so the measure-theoretic assembly can be checked independently of the
Gaussian variance calculation. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open ConditionedDeterminantMoments SphericalTAPCriticalAnalyticNeighborhood
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

def originalLatitudeBankPoint {d : ℕ} (μ : FiniteMixture) (a β : ℝ)
    (u : Vector (d+2)) (J : Disorder (d+2) μ.maxDegree)
    (y : Vector (d+1)) : ℝ :=
  Real.exp (β*field (mixtureCoefficients μ) J
    (originalLatitudePoint a u (quadraticBankDirection (d+1) u y)))

def originalLatitudeBankPartition {d : ℕ} (μ : FiniteMixture) (a β : ℝ)
    (u : Vector (d+2)) (J : Disorder (d+2) μ.maxDegree) : ℝ :=
  ∫ y : Vector (d+1), originalLatitudeBankPoint μ a β u J y ∂sphereLaw (d+1)

theorem latitudeMap_eq_originalLatitudePoint {d : ℕ} (u : Vector (d+2))
    (a : ℝ) (y : Vector (d+1)) :
    latitudeMap u (latitudeFrameAt u) a y =
      originalLatitudePoint a u (quadraticBankDirection (d+1) u y) := by
  have hratio : 0 ≤ (((d+2:ℕ):ℝ)/((d+1:ℕ):ℝ)) := by positivity
  simp only [latitudeMap,originalLatitudePoint,quadraticBankDirection,smul_smul]
  rw [Real.sqrt_mul hratio]
  ring

theorem originalLatitudeBankPartition_eq_physical {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2))
    (J : Disorder (d+2) μ.maxDegree) :
    originalLatitudeBankPartition μ a β u J =
      partitionAgainst (latitudeLaw u (latitudeFrameAt u) a) β
        (field (mixtureCoefficients μ) J) := by
  rw [latitudePartition_eq_sphereIntegral]
  unfold originalLatitudeBankPartition originalLatitudeBankPoint
  congr 1
  funext y
  rw [latitudeMap_eq_originalLatitudePoint]

theorem originalLatitudeBankPoint_joint_measurable {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2)) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      originalLatitudeBankPoint μ a β u z.1 z.2) := by
  have hf := field_jointContinuous (N := d+2) (mixtureCoefficients μ)
  unfold originalLatitudeBankPoint originalLatitudePoint quadraticBankDirection
  fun_prop

theorem originalLatitudeBankPoint_integrable_direction {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2))
    (J : Disorder (d+2) μ.maxDegree) :
    Integrable (originalLatitudeBankPoint μ a β u J) (sphereLaw (d+1)) := by
  have hf := (field_contDiff (mixtureCoefficients μ) J).continuous
  have hc : Continuous (originalLatitudeBankPoint μ a β u J) := by
    unfold originalLatitudeBankPoint originalLatitudePoint quadraticBankDirection
    fun_prop
  exact SphericalForm.integrable_sphereSupported_continuous (sphereLaw (d+1))
    (sphereLaw_support (by omega)) hc

theorem originalLatitudeBankPartition_measurable {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2)) :
    Measurable (originalLatitudeBankPartition μ a β u) := by
  exact (originalLatitudeBankPoint_joint_measurable μ a β u).stronglyMeasurable
    |>.integral_prod_right' |>.measurable

/-- Angular Fubini upgrades the exact pointwise residual factorization to
the actual latitude partition. The pointwise exponential integrability and
common residual moment will follow from the Gaussian posterior calculation. -/
theorem mixed_palm_determinant_latitude_angular_factorization
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (hnp : μ.minDegree < μ.maxDegree) {Q : ℝ} (hQ : 0 < Q)
    (a β : ℝ) (ha : 0 ≤ 1-a^2)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) (c : ℝ)
    (hpointInt : ∀ y : Vector (d+1),
      Integrable (fun J => intrinsicDet μ Q u J *
        originalLatitudeBankPoint μ a β u J y)
        (mixedLaw μ Q u hu mark))
    (hres : ∀ y : Vector (d+1), ‖y‖^2=((d+1:ℕ):ℝ) →
      (∫ J, Real.exp (β*(field (mixtureCoefficients μ) J
          (originalLatitudePoint a u (quadraticBankDirection (d+1) u y)) -
        quadraticLatitudeJet μ a u (quadraticBankDirection (d+1) u y) J))
        ∂mixedLaw μ Q u hu mark) = c)
    (hbankInt : Integrable (fun J => intrinsicDet μ Q u J *
      quadraticBankPartition μ a β u J) (mixedLaw μ Q u hu mark)) :
    Integrable (fun J => intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J)
      (mixedLaw μ Q u hu mark) ∧
    (∫ J, intrinsicDet μ Q u J *
      originalLatitudeBankPartition μ a β u J
      ∂mixedLaw μ Q u hu mark) =
      c * (∫ J, intrinsicDet μ Q u J *
        quadraticBankPartition μ a β u J
        ∂mixedLaw μ Q u hu mark) := by
  let ν := mixedLaw μ Q u hu mark
  let ρ := sphereLaw (d+1)
  let D := intrinsicDet μ Q u
  let F := originalLatitudeBankPoint μ a β u
  let G := quadraticBankPoint μ a β u
  haveI : IsProbabilityMeasure ν := by
    dsimp [ν,mixedLaw]
    infer_instance
  have hDmeas : Measurable D := by
    unfold D intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hD0 (J : Disorder (d+2) μ.maxDegree) : 0 ≤ D J := abs_nonneg _
  have hGjoint : Measurable (fun w : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      D w.1 * G w.1 w.2) :=
    (hDmeas.comp measurable_fst).mul
      (quadraticBankPoint_joint_measurable μ a β u)
  have hswap : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      (w.2,w.1)) := measurable_snd.prodMk measurable_fst
  have hFm : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      F w.2 w.1) := by
    simpa only [F,Function.comp_def,Prod.fst,Prod.snd] using
      (originalLatitudeBankPoint_joint_measurable μ a β u).comp hswap
  have hFjoint : Measurable (fun w : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      D w.2 * F w.2 w.1) := (hDmeas.comp measurable_snd).mul hFm
  have hpoint : ∀ᵐ y ∂ρ,
      (∫ J, D J * F J y ∂ν) = c*(∫ J, D J * G J y ∂ν) := by
    filter_upwards [sphereLaw_support (by omega : 1 ≤ d+1)] with y hy
    have hh := mixed_palm_determinant_latitude_factorization
      μ hμ hnp hQ a β ha u (quadraticBankDirection (d+1) u y)
      hu (quadraticBankDirection_tangent u hu y) mark
    rw [hres y hy] at hh
    simpa only [D,F,G,originalLatitudeBankPoint,quadraticBankPoint] using hh
  exact PositiveAngularFactorization.weighted_integral_factorization
    ν ρ D F G c hD0
    (fun J y => (Real.exp_pos _).le)
    (fun J y => (Real.exp_pos _).le)
    hGjoint hFjoint
    (fun J => quadraticBankPoint_integrable_direction μ a β u J)
    hpointInt hpoint hbankInt

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
