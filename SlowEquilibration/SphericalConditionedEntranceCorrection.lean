module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.ConditionedEntranceRegressionOrders
public import SlowEquilibration.SphericalForm
public import SlowEquilibration.SphericalGaussianJet

@[expose] public section

/-!
# The literal spherical regression correction and its actual gradient

In the nonpure branch, the correction is the manuscript polynomial, with the true finite mixed
field value, radial jet, and intrinsic gradient at the center. This file
proves its differential formula by the ordinary product and chain rules.
It does not assert a cap-hitting estimate or identify the correction law
with the whole-field Gaussian posterior.
-/

namespace SlowEquilibration.ConditionedEntrance
noncomputable section
open SphericalModel SphericalForm SphericalGaussianJet
open scoped RealInnerProductSpace
variable {N : ℕ}

/-- The literal correction polynomial, with the observed center quantities
left as explicit arguments for its deterministic calculus. -/
def regressionCorrection (μ : FiniteMixture) (Q : ℝ) (u G : Vector N)
    (Hq Kq h k : ℝ) (x : Vector N) : ℝ :=
  valueTheta μ Q (overlap x u) * ((N : ℝ) * h - Hq) +
  radialTheta μ Q (overlap x u) * ((N : ℝ) * k - Kq) -
  tangentTheta μ Q (overlap x u) * inner ℝ G x

/-- Exact scalar coefficient of the radial part of the correction gradient. -/
def correctionRadialCoefficient (μ : FiniteMixture) (Q : ℝ) (u G : Vector N)
    (Hq Kq h k : ℝ) (x : Vector N) : ℝ :=
  valueThetaDerivative μ Q (overlap x u) * ((N : ℝ) * h - Hq) +
  radialThetaDerivative μ Q (overlap x u) * ((N : ℝ) * k - Kq) -
  tangentThetaDerivative μ Q (overlap x u) * inner ℝ G x

/-- The ambient Riesz gradient is derived from the exact polynomial chain
rule, with the manuscript normalization `1/N`. -/
theorem regressionCorrection_hasGradientAt (μ : FiniteMixture) (Q : ℝ)
    (u G : Vector N) (Hq Kq h k : ℝ) (x : Vector N) :
    HasGradientAt (regressionCorrection μ Q u G Hq Kq h k)
      ((correctionRadialCoefficient μ Q u G Hq Kq h k x / (N : ℝ)) • u -
        tangentTheta μ Q (overlap x u) • G) x := by
  have hR : HasFDerivAt (fun y : Vector N => overlap y u)
      ((N : ℝ)⁻¹ • innerSL ℝ u) x := by
    have hd := ((innerSL ℝ u).hasFDerivAt (x := x)).const_mul (N : ℝ)⁻¹
    convert hd using 1
    funext y
    simp only [overlap, div_eq_inv_mul]
    rw [real_inner_comm]
    rfl
  have hG := (innerSL ℝ G).hasFDerivAt (x := x)
  have h1 := ((valueTheta_hasDerivAt μ Q (overlap x u)).comp_hasFDerivAt x hR).mul_const
    ((N : ℝ) * h - Hq)
  have h2 := ((radialTheta_hasDerivAt μ Q (overlap x u)).comp_hasFDerivAt x hR).mul_const
    ((N : ℝ) * k - Kq)
  have h3 := ((tangentTheta_hasDerivAt μ Q (overlap x u)).comp_hasFDerivAt x hR).mul hG
  have hd := (h1.add h2).sub h3
  apply hd.congr_fderiv
  ext v
  simp only [correctionRadialCoefficient, add_apply,
    sub_apply, _root_.smul_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, inner_sub_left, real_inner_smul_left,
    innerSL_apply_apply, Function.comp_apply]
  ring

/-- The actual intrinsic gradient formula `eq:ent-correction-gradient`.
Projection is the literal spherical orthogonal projection `I-xxᵀ/N`. -/
theorem regressionCorrection_surfaceGradient (μ : FiniteMixture) (Q : ℝ)
    (u G : Vector N) (Hq Kq h k : ℝ) (x : Vector N) :
    surfaceGradient (regressionCorrection μ Q u G Hq Kq h k) x =
      (correctionRadialCoefficient μ Q u G Hq Kq h k x / (N : ℝ)) •
        tangentProjection x u - tangentTheta μ Q (overlap x u) • tangentProjection x G := by
  rw [surfaceGradient, (regressionCorrection_hasGradientAt μ Q u G Hq Kq h k x).gradient,
    map_sub, map_smul, map_smul]

/-- The source correction, now attached to the actual mixed center field. -/
def sourceRegressionCorrection (μ : FiniteMixture) (Q : ℝ)
    (_hQ : 0 < Q) (_hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (u : Vector N) (h k : ℝ) : Vector N → ℝ :=
  let c := centerCoefficients (mixtureCoefficients μ) Q
  regressionCorrection μ Q u (surfaceGradient (field c J) u)
    (field c J u) (jet c 1 u (fun _ => u) J) h k

/-- The preceding differential formula specializes to the literal field,
without an assumed gradient representation or covariance-matching model. -/
theorem sourceRegressionCorrection_surfaceGradient (μ : FiniteMixture) (Q : ℝ)
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (J : Disorder N μ.maxDegree) (u : Vector N) (h k : ℝ) (x : Vector N) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    surfaceGradient (sourceRegressionCorrection μ Q hQ hnp J u h k) x =
      (correctionRadialCoefficient μ Q u (surfaceGradient (field c J) u)
        (field c J u) (jet c 1 u (fun _ => u) J) h k x / (N : ℝ)) •
        tangentProjection x u - tangentTheta μ Q (overlap x u) •
          tangentProjection x (surfaceGradient (field c J) u) :=
  regressionCorrection_surfaceGradient _ _ _ _ _ _ _ _ _

end
end SlowEquilibration.ConditionedEntrance
