-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDiracCovariance
public import SlowEquilibration.SphericalPlateauAmplitudeDirections

@[expose] public section

/-! # The literal fixed-atom Dirac trial for the source amplitude bank

The true Crisanti--Sommers Dirac functional is evaluated at the original
atom. The selected amplitude line changes its value by the exact source
coefficient τ(2+τ)β²a_k²(1-t^k)/2.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel
open scoped Topology BigOperators
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original atom remains fixed when the source amplitudes change. -/
def amplitudeDiracTrial (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) (r : ℝ) : ℝ :=
  (β^2*(amplitudeLatitudeCovariance μ p₀ s r 1-
    amplitudeLatitudeCovariance μ p₀ s r (amplitudeDiracAtom r))+
    amplitudeDiracAtom r/(1-amplitudeDiracAtom r)+Real.log (1-amplitudeDiracAtom r))/2

theorem amplitudeDiracTrial_eq_functional (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) (r : ℝ) :
    amplitudeDiracTrial μ β p₀ s r=
      CrisantiSommers.functional β (amplitudeTransverseCovariance μ p₀ s r)
        (Measure.dirac (amplitudeDiracAtom r)) (amplitudeDiracAtom r) := by
  rw [CrisantiSommers.functional_dirac β _ (amplitudeDiracAtom_mem r)]
  unfold amplitudeDiracTrial amplitudeTransverseCovariance
  ring

/-- The unperturbed trial is exactly the original latitude RS trial at
the absolute latitude; this retains both signs in the actual bank. -/
theorem amplitudeDiracTrial_one (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    {r : ℝ} (hr : |r|<1) :
    amplitudeDiracTrial μ β p₀ (fun _ => 1) r=latitudePressureTrial μ β |r| := by
  rw [amplitudeDiracTrial_eq_functional,amplitudeTransverseCovariance_one]
  have hcov : μ.auxiliaryCovariance r=μ.auxiliaryCovariance |r| := by
    funext t
    unfold FiniteMixture.auxiliaryCovariance
    rw [sq_abs]
  rw [hcov,show amplitudeDiracAtom r=CrisantiSommers.latitudeDiracLocation |r| by rfl]
  exact CrisantiSommers.functional_auxiliary_dirac μ β ⟨abs_nonneg r,hr⟩

def amplitudeSelectedIndex (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (k : Fin 2) : BankIndex μ :=
  ⟨p₀,⟨k.val+1,by have hp := p₀.property;have hk := k.isLt;omega⟩⟩

def amplitudeSelectedCoefficient (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (r : ℝ) : ℝ :=
  mixtureCoefficients μ p₀*(Nat.choose p₀.val.val (k.val+1) : ℝ)*
    r^(2*(p₀.val.val-(k.val+1)))*(1-r^2)^(k.val+1)

/-- Exact change of the literal latitude covariance along one source
amplitude direction, retaining every other actual Gaussian bank coordinate. -/
theorem amplitudeLatitudeCovariance_at (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ r t : ℝ) :
    amplitudeLatitudeCovariance μ p₀ (amplitudeAt k τ) r t=
      amplitudeLatitudeCovariance μ p₀ (fun _ => 1) r t+
        τ*(2+τ)*amplitudeSelectedCoefficient μ p₀ k r*t^(k.val+1) := by
  classical
  let i₀ := amplitudeSelectedIndex μ p₀ k
  have hsel (i : BankIndex μ) : (i.1=p₀ ∧ i.2.val=k.val+1) ↔ i=i₀ := by
    constructor
    · rintro ⟨hp,hk⟩
      cases i with
      | mk p j =>
          dsimp only at hp hk
          subst p
          exact congrArg (Sigma.mk p₀) (Fin.ext hk)
    · rintro rfl
      exact ⟨rfl,rfl⟩
  have hp (i : BankIndex μ) : amplitudeLatitudeCoefficient μ p₀ (amplitudeAt k τ) r i*t^i.2.val=
      amplitudeLatitudeCoefficient μ p₀ (fun _ => 1) r i*t^i.2.val+
        τ*(2+τ)*(if i=i₀ then amplitudeLatitudeCoefficient μ p₀ (fun _ => 1) r i*t^i.2.val else 0) := by
    unfold amplitudeLatitudeCoefficient
    rw [bankAmplitude_at,bankAmplitude_one]
    simp only [hsel]
    by_cases hi : i=i₀ <;> simp only [hi,ite_true,ite_false,one_pow,one_mul,mul_zero] <;> ring
  simp only [amplitudeLatitudeCovariance_eq_polynomial,FiniteNonnegativePolynomial.covariance]
  simp_rw [hp]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  dsimp only [i₀,amplitudeSelectedIndex,amplitudeLatitudeCoefficient,amplitudeSelectedCoefficient]
  rw [bankAmplitude_one]
  simp only [one_pow,one_mul]
  ring

def amplitudeDiracShiftCoefficient (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (r : ℝ) : ℝ :=
  (β^2/2)*amplitudeSelectedCoefficient μ p₀ k r*(1-(amplitudeDiracAtom r)^(k.val+1))

/-- Exact source envelope shift of the actual fixed original Dirac trial. -/
theorem amplitudeDiracTrial_at (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ r : ℝ) :
    amplitudeDiracTrial μ β p₀ (amplitudeAt k τ) r=
      amplitudeDiracTrial μ β p₀ (fun _ => 1) r+τ*(2+τ)*amplitudeDiracShiftCoefficient μ β p₀ k r := by
  unfold amplitudeDiracTrial amplitudeDiracShiftCoefficient
  rw [amplitudeLatitudeCovariance_at,amplitudeLatitudeCovariance_at]
  simp only [one_pow]
  ring

theorem amplitudeLatitudeCovariance_joint_continuous (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) :
    Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => amplitudeLatitudeCovariance μ p₀ z.1.1 z.1.2 z.2) := by
  simp only [amplitudeLatitudeCovariance_eq_polynomial,FiniteNonnegativePolynomial.covariance]
  exact continuous_finsetSum _ fun i _ =>
    ((amplitudeLatitudeCoefficient_joint_continuous μ p₀ i).comp continuous_fst).mul (continuous_snd.pow _)

theorem amplitudeLatitudeCovarianceFirst_joint_continuous (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) :
    Continuous (fun z : ((Fin 2 → ℝ) × ℝ) × ℝ => amplitudeLatitudeCovarianceFirst μ p₀ z.1.1 z.1.2 z.2) := by
  unfold amplitudeLatitudeCovarianceFirst FiniteNonnegativePolynomial.firstDerivative
  exact continuous_finsetSum _ fun i _ =>
    (((amplitudeLatitudeCoefficient_joint_continuous μ p₀ i).comp continuous_fst).mul continuous_const).mul
      (continuous_snd.pow _)

theorem amplitudeDiracTrial_joint_continuous (μ : FiniteMixture) (β : ℝ) (p₀ : Degree μ.maxDegree) :
    Continuous (fun z : (Fin 2 → ℝ) × ℝ => amplitudeDiracTrial μ β p₀ z.1 z.2) := by
  unfold amplitudeDiracTrial
  let X := (Fin 2 → ℝ) × ℝ
  have hA : Continuous (fun z : X => amplitudeDiracAtom z.2) :=
    amplitudeDiracAtom_continuous.comp (continuous_snd : Continuous (fun z : X => z.2))
  have hden : ∀ z : X,1-amplitudeDiracAtom z.2≠0 := fun z => by
    have hh := (amplitudeDiracAtom_mem z.2).2
    linarith
  have he1 : Continuous (fun z : X => (z,(1 : ℝ))) :=
    (continuous_id : Continuous (fun z : X => z)).prodMk continuous_const
  have het : Continuous (fun z : X => (z,amplitudeDiracAtom z.2)) :=
    (continuous_id : Continuous (fun z : X => z)).prodMk hA
  have h1 : Continuous (fun z : X => amplitudeLatitudeCovariance μ p₀ z.1 z.2 1) := by
    simpa only [Function.comp_def] using (amplitudeLatitudeCovariance_joint_continuous μ p₀).comp he1
  have ht : Continuous (fun z : X => amplitudeLatitudeCovariance μ p₀ z.1 z.2 (amplitudeDiracAtom z.2)) := by
    simpa only [Function.comp_def] using (amplitudeLatitudeCovariance_joint_continuous μ p₀).comp het
  have he := (h1.sub ht).const_mul (β^2)
  have hq := hA.div (continuous_const.sub hA) hden
  have hl := (continuous_const.sub hA).log hden
  have hh := ((he.add hq).add hl).div_const 2
  convert hh using 1

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
