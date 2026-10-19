-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairChartKacRice
public import SlowEquilibration.SphericalIntrinsicKacRice

/-! Literal ordered pairs of actual spherical critical points, including
arbitrary whole-disorder marks, and genuine almost-sure chart gluing. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairCountGluing
open MeasureTheory ProbabilityTheory Set Function Metric
open SphericalModel SphericalForm SphericalGaussianJet WholeFieldRegression
open SphericalChartKacRice SphereChartVolume SphericalChartGeometry SphereHessian
open SphericalPairChartGeometry SphericalPairChartKacRice SphericalKacRiceGluing
open scoped RealInnerProductSpace ENNReal Topology
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual ordered pair count on the actual radius sphere, restricted
only by the overlap window and by the two true critical equations. -/
def actualSpherePairCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (ρ : ℝ)
    (psi : Disorder (n+1) P → Vector (n+1) × Vector (n+1) → ℝ≥0∞)
    (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' p : {p : Vector (n+1) × Vector (n+1) |
    ‖p.1‖^2=(n+1:ℕ) ∧ ‖p.2‖^2=(n+1:ℕ) ∧ |overlap p.1 p.2| < ρ ∧
    surfaceGradient (field c J) p.1=0 ∧ surfaceGradient (field c J) p.2=0},psi J p

def pairChartMap (n : ℕ) (p : PairChart n) : Vector (n+1) × Vector (n+1) :=
  (manuscriptChart n p.fst,manuscriptChart n p.snd)

lemma pairChartMap_continuous (n : ℕ) : Continuous (pairChartMap n) := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))
  exact ((RoundSphereChartIntegral.manuscriptChart_continuous n).comp e.continuous.fst).prodMk
    ((RoundSphereChartIntegral.manuscriptChart_continuous n).comp e.continuous.snd)

/-- Actual pair counts agree with the single product chart whenever its
one omitted pole is noncritical. No finiteness or Morse assumption is used. -/
theorem actualSpherePairCount_eq_chart_of_noncritical_pole {P : ℕ} (n : ℕ)
    (c : Degree P → ℝ) (ρ : ℝ)
    (psi : Disorder (n+1) P → Vector (n+1) × Vector (n+1) → ℝ≥0∞)
    (J : Disorder (n+1) P) (hpole : surfaceGradient (field c J) (southPole n)≠0) :
    actualSpherePairCount n c ρ psi J=
      actualPairChartCount n c (pairOverlapDomain n ρ) (fun J p => psi J (pairChartMap n p)) J := by
  classical
  let C := {p : PairChart n | p ∈ pairOverlapDomain n ρ ∧
    surfaceGradient (field c J) (manuscriptChart n p.fst)=0 ∧
    surfaceGradient (field c J) (manuscriptChart n p.snd)=0}
  let S := {p : Vector (n+1) × Vector (n+1) |
    ‖p.1‖^2=(n+1:ℕ) ∧ ‖p.2‖^2=(n+1:ℕ) ∧ |overlap p.1 p.2| < ρ ∧
    surfaceGradient (field c J) p.1=0 ∧ surfaceGradient (field c J) p.2=0}
  let f : C → S := fun p => ⟨pairChartMap n p,
    manuscriptChart_norm_sq p.property.1.1.1,manuscriptChart_norm_sq p.property.1.1.2,
    p.property.1.2,p.property.2⟩
  have hi : Injective f := by
    intro p q he
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact SphericalKacRiceGluing.manuscriptChart_injOn n
        (by simpa using p.property.1.1.1) (by simpa using q.property.1.1.1)
        (congrArg (fun z : S => z.val.1) he)
    · exact SphericalKacRiceGluing.manuscriptChart_injOn n
        (by simpa using p.property.1.1.2) (by simpa using q.property.1.1.2)
        (congrArg (fun z : S => z.val.2) he)
  have hs : Surjective f := by
    intro p
    have hx : p.val.1 ≠ southPole n := by
      intro he
      exact hpole (he ▸ p.property.2.2.2.1)
    have hy : p.val.2 ≠ southPole n := by
      intro he
      exact hpole (he ▸ p.property.2.2.2.2)
    have hxc : p.val.1 ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨p.property.1,hx⟩
    have hyc : p.val.2 ∈ manuscriptChart n '' ball 0 2 := by
      rw [manuscriptChart_image_ball_except_pole]
      exact ⟨p.property.2.1,hy⟩
    obtain ⟨u,hu,heu⟩ := hxc
    obtain ⟨v,hv,hev⟩ := hyc
    let q : PairChart n := WithLp.toLp 2 (u,v)
    have hq : q ∈ pairOverlapDomain n ρ := by
      refine ⟨⟨by simpa [q] using hu,by simpa [q] using hv⟩,?_⟩
      change |overlap (manuscriptChart n u) (manuscriptChart n v)| < ρ
      rw [heu,hev]
      exact p.property.2.2.1
    have hq1 : surfaceGradient (field c J) (manuscriptChart n q.fst)=0 := by
      change surfaceGradient (field c J) (manuscriptChart n u)=0
      rw [heu]
      exact p.property.2.2.2.1
    have hq2 : surfaceGradient (field c J) (manuscriptChart n q.snd)=0 := by
      change surfaceGradient (field c J) (manuscriptChart n v)=0
      rw [hev]
      exact p.property.2.2.2.2
    refine ⟨⟨q,hq,hq1,hq2⟩,?_⟩
    apply Subtype.ext
    exact Prod.ext heu hev
  let e : C ≃ S := Equiv.ofBijective f ⟨hi,hs⟩
  exact (e.tsum_eq (fun p : S => psi J p)).symm

/-- Genuine global pair Kac--Rice, with literal sphere critical pairs on
the left and the independently proved product-chart integral on the right.
All covariance, pole-removal, and chart-cover premises are discharged. -/
theorem actual_sphere_pair_chart_kacRice (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hdeg : 4 ≤ μ.minDegree)
    (psi : Disorder (n+1) μ.maxDegree → Vector (n+1) × Vector (n+1) → ℝ≥0∞)
    (hpsi : Measurable fun p : Disorder (n+1) μ.maxDegree × (Vector (n+1) × Vector (n+1)) => psi p.1 p.2) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let ρ := pairRadius μ hQ hdeg
    AEMeasurable (actualSpherePairCount n c ρ psi) (disorderLaw (n+1) μ.maxDegree) ∧
    (∫⁻ J,actualSpherePairCount n c ρ psi J ∂disorderLaw (n+1) μ.maxDegree)=
      ∫⁻ p in pairOverlapDomain n ρ, GaussianRegression.observationPdf (pairChartGamma n c p) 0 *
        (ENNReal.ofReal (manuscriptChartGram n p.fst).det * ENNReal.ofReal (manuscriptChartGram n p.snd).det) *
        ∫⁻ J, (ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.fst)).det| *
          ENNReal.ofReal |(intrinsicHessian (field c J) (manuscriptChart n p.snd)).det|) * psi J (pairChartMap n p)
            ∂coefficientKernel (pairChartGamma n c p) 0 := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let ρ := pairRadius μ hQ hdeg
  have hm := hpsi.comp (measurable_fst.prodMk ((pairChartMap_continuous n).measurable.comp measurable_snd))
  have hk := actual_pair_chart_smallOverlap_kacRice n μ hQ hdeg (fun J p => psi J (pairChartMap n p)) hm
  have hpole := SphericalIntrinsicKacRice.fixed_point_noncritical_ae n hn μ hQ (southPole n) (southPole_norm_sq n)
  have he : actualSpherePairCount n c ρ psi =ᵐ[disorderLaw (n+1) μ.maxDegree]
      actualPairChartCount n c (pairOverlapDomain n ρ) (fun J p => psi J (pairChartMap n p)) := by
    filter_upwards [hpole] with J hJ
    exact actualSpherePairCount_eq_chart_of_noncritical_pole n c ρ psi J hJ
  exact ⟨hk.1.congr he.symm,(lintegral_congr_ae he).trans hk.2⟩

end SlowEquilibration.SphericalPairCountGluing
