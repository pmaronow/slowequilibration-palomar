module

public import SlowEquilibration.PalomarCondensedInitial
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

set_option backward.proofsInPublic true

@[expose] public section
noncomputable section
namespace SlowEquilibrationCondensedSource
open Set MeasureTheory Filter
open scoped Topology BigOperators

def staticThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt (sInf ((fun r : ℝ => (-r-Real.log (1-r))/ξ r) '' Ioo 0 1))

def dynamicalThreshold (ξ : ℝ → ℝ) : ℝ :=
  Real.sqrt ((sSup ((fun r : ℝ => (1-r)*deriv ξ r/r) '' Ioo 0 1))⁻¹)

def qStar (ξ : ℝ → ℝ) (β : ℝ) : ℝ :=
  sSup {r : ℝ | r ∈ Ioo 0 1 ∧ 1 < β^2*((1-r)*deriv ξ r/r)}

def inverseSqrt (v : ℝ → ℝ) : ℝ → ℝ := fun r => (Real.sqrt (v r))⁻¹

def pureCovariance (p : ℕ) (hp : 2 ≤ p) : FiniteMixture where
  coeff := Finsupp.single p 1
  nonneg := by intro q; by_cases h : q=p <;> simp [h]
  zero_below_two := by
    intro q hq
    have h : q≠p := by omega
    simp [h]
  nonzero := by
    intro h
    have h' := congrArg (fun f : ℕ →₀ ℝ => f p) h
    simp at h'

structure ClassPerturbation (d P : ℕ) where
  coeff : ℕ →₀ ℝ
  nonneg : ∀ p, 0 ≤ coeff p
  zero_of_le : ∀ p, p ≤ d → coeff p = 0
  zero_of_gt : ∀ p, P < p → coeff p = 0
  even_supported : ∀ p ∈ coeff.support, Even p
  total_le_one : coeff.sum (fun _ c => c) ≤ 1

def ClassPerturbation.covariance {d P : ℕ} (b : ClassPerturbation d P)
    (hd : 3 ≤ d) (ε : ℝ) (hε : 0 ≤ ε) : FiniteMixture where
  coeff := Finsupp.single d 1 + ε • b.coeff
  nonneg := by
    intro p
    apply add_nonneg
    · by_cases hp : p=d <;> simp [hp]
    · exact mul_nonneg hε (b.nonneg p)
  zero_below_two := by
    intro p hp
    have hpd : p≠d := by omega
    simp [hpd, b.zero_of_le p (by omega)]
  nonzero := by
    intro hz
    have h := congrArg (fun f : ℕ →₀ ℝ => f d) hz
    simp [b.zero_of_le d le_rfl] at h

def exampleParameter : ℝ := (45-24*Real.log 6)/(72*Real.log 6-85)
def exampleB : ℝ := exampleParameter*(10/9 : ℝ)^8
def exampleBeta : ℝ := Real.sqrt (15/((9/10 : ℝ)^3*(4+12*exampleParameter)))

theorem exampleB_pos : 0 < exampleB := by
  have harg : (1+(5/7 : ℝ))/(1-(5/7 : ℝ))=6 := by norm_num
  have hlo := Real.sum_range_le_log_div (x := (5/7 : ℝ))
    (by norm_num) (by norm_num) 1
  have hhi := Real.log_div_le_sum_range_add (x := (5/7 : ℝ))
    (by norm_num) (by norm_num) 6
  rw [harg] at hlo hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have ht : 0 < exampleParameter := by
    unfold exampleParameter
    apply div_pos <;> linarith
  exact mul_pos ht (by positivity)

def exampleCovariance : FiniteMixture where
  coeff := Finsupp.single 4 1 + Finsupp.single 12 exampleB
  nonneg := by
    intro p
    apply add_nonneg
    · by_cases hp : p=4 <;> simp [hp]
    · by_cases hp : p=12 <;> simp [hp, exampleB_pos.le]
  zero_below_two := by
    intro p hp
    have h4 : p≠4 := by omega
    have h12 : p≠12 := by omega
    simp [h4,h12]
  nonzero := by
    intro h
    have h' := congrArg (fun f : ℕ →₀ ℝ => f 4) h
    norm_num at h'

def UniformConclusions (μ : FiniteMixture) (β : ℝ) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧ uniformSeparation μ β γ

universe u v

/-- Exactly the three initial-law clauses, with the common uniform exponent. -/
def SixInitialConclusions (μ : FiniteMixture) (β γ : ℝ) : Prop :=
  let T := fun N => exponentialHorizon γ N
  CondensedAndInitial μ β γ ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (ν : ∀ N, ι N → Measure (Vector N)) [∀ N j, IsProbabilityMeasure (ν N j)],
      (∀ N, 2 ≤ N → ∀ j, ∀ᵐ y ∂ν N j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereMenuDistance μ β (ν N) (T N)) 1) ∧
  (∀ (ι : ℕ → Type u) [∀ N, Fintype (ι N)] [∀ N, Nonempty (ι N)]
      (R : ℕ → Type v) [∀ N, MeasurableSpace (R N)]
      (ρ : ∀ N, Measure (R N)) [∀ N, IsProbabilityMeasure (ρ N)]
      (ν : ∀ N, R N → ι N → Measure (Vector N)),
      (∀ N j, Measurable (fun r => ν N r j)) →
      ∀ [∀ N r j, IsProbabilityMeasure (ν N r j)],
      (∀ N, 2 ≤ N → ∀ r j, ∀ᵐ y ∂ν N r j, OnSphere y) →
      ∀ κ C₀ : ℝ, 0 ≤ κ → κ < ((μ.minDegree : ℝ)-2)/2 → 0 < C₀ →
      (∀ᶠ N in atTop, (Fintype.card (ι N) : ℝ) ≤ C₀*(N : ℝ)^κ) →
      inProbability (fun N => (ρ N).prod (sphereFieldLaw N μ))
        (fun N z => sphereMenuDistance μ β (ν N z.1) (T N) z.2) 1) ∧
  (∀ (κ : ∀ N, ProbabilityTheory.Kernel (SphereField N μ) (Vector N))
      [∀ N, ProbabilityTheory.IsMarkovKernel (κ N)],
      (∀ N, 2 ≤ N → ∀ H, ∀ᵐ y ∂κ N H, OnSphere y) →
      littleLogInProbability (fun N => sphereFieldLaw N μ)
        (fun N H => InformationTheory.klDiv (κ N H) (sphereLaw N)) →
      inProbability (fun N => sphereFieldLaw N μ)
        (fun N => sphereIntervalDistance μ β (T N) (κ N)) 1)

end SlowEquilibrationCondensedSource
