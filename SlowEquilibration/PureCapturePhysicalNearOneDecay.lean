-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalNearOneAverageBridge
public import SlowEquilibration.ExponentialEnergyAbsorption

/-! The original disorder-averaged Gibbs pair has a fixed near-one cap
whose probability tends to zero at every nonnegative inverse temperature.
The Gaussian field-good tail and spherical cap entropy are both proved
for the actual mixed tensor Hamiltonian. -/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open SlowEquilibration SphericalModel SphericalForm
open SlowEquilibration.PureCapturePhysicalNearOneAverage
open SlowEquilibration.PureCapturePhysicalFullOverlapArray
open SlowEquilibration.PureCapturePhysicalReplicaExclusionLimit
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace SlowEquilibration.PureCapturePhysicalNearOneDecay

theorem exists_entropy_beating_latitude
    {β K : ℝ} (hβ : 0 ≤ β) (hK : 0 ≤ K) :
    ∃ a s : ℝ, 0 < a ∧ a < s ∧ s < 1 ∧
      Tendsto (fun n : ℕ =>
        2*(Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
          (4*Real.sqrt ((n+1 : ℕ) : ℝ)*
            (Real.sqrt (1-a^2))^(n-1)))) atTop (𝓝 0) := by
  let C : ℝ := 2*β*K+2
  have hC : 0 < C := by dsimp [C]; nlinarith [mul_nonneg hβ hK]
  let a : ℝ := Real.sqrt (1-Real.exp (-2*C))
  let s : ℝ := (a+1)/2
  have hE : 0 < Real.exp (-2*C) ∧ Real.exp (-2*C) < 1 := by
    constructor
    · exact Real.exp_pos _
    · rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by linarith)
  have ha0 : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (by linarith [hE.2])
  have ha1 : a < 1 := by
    dsimp [a]
    nlinarith [Real.sq_sqrt (show 0 ≤ 1-Real.exp (-2*C) by linarith), hE.1]
  have has : a < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hbase : Real.sqrt (1-a^2) = Real.exp (-C) := by
    have ha2 : a^2 = 1-Real.exp (-2*C) :=
      Real.sq_sqrt (by linarith [hE.2])
    rw [ha2, show 1-(1-Real.exp (-2*C)) = Real.exp (-2*C) by ring]
    rw [show -2*C = (2 : ℕ)*(-C) by push_cast; ring,
      Real.exp_nat_mul, Real.sqrt_sq_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  refine ⟨a, s, ha0, has, hs1, ?_⟩
  have hN : Tendsto (fun n : ℕ => ((n+1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun n : ℕ =>
      (((n+1 : ℕ) : ℝ) ^ ((1/2 : ℝ))) *
        Real.exp (-2*((n+1 : ℕ) : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2 : ℝ) 2
      (by norm_num)).comp hN
  have hevent : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  have heq (n : ℕ) (hn : 1 ≤ n) :
      2*(Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
        (4*Real.sqrt ((n+1 : ℕ) : ℝ)*
          (Real.sqrt (1-a^2))^(n-1))) =
      (8*Real.exp (3*C-2)) *
        ((((n+1 : ℕ) : ℝ) ^ ((1/2 : ℝ))) *
          Real.exp (-2*((n+1 : ℕ) : ℝ))) := by
    rw [hbase, Real.sqrt_eq_rpow, ← Real.exp_nat_mul]
    have hcast : (((n-1 : ℕ) : ℝ)) = ((n+2 : ℕ) : ℝ)-3 := by
      rw [Nat.cast_sub hn]
      push_cast
      ring
    rw [hcast]
    have hexp : Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
        Real.exp ((((n+2 : ℕ) : ℝ)-3)*(-C)) =
        Real.exp (3*C-2) * Real.exp (-2*((n+1 : ℕ) : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      dsimp [C]
      push_cast
      ring
    calc
      _ = 8*(((n+1 : ℕ) : ℝ) ^ ((1/2 : ℝ))) *
          (Real.exp (2*β*K*((n+2 : ℕ) : ℝ)) *
            Real.exp ((((n+2 : ℕ) : ℝ)-3)*(-C))) := by ring
      _ = 8*(((n+1 : ℕ) : ℝ) ^ ((1/2 : ℝ))) *
          (Real.exp (3*C-2) * Real.exp (-2*((n+1 : ℕ) : ℝ))) := by rw [hexp]
      _ = _ := by ring
  have htarget := ht.const_mul (8*Real.exp (3*C-2))
  simpa only [mul_zero] using htarget.congr' (hevent.mono fun n hn => (heq n hn).symm)

/-- The original disorder-averaged two-replica spherical Gibbs law has
vanishing mass in one fixed near-one overlap cap at every nonnegative
inverse temperature. The cap threshold is chosen before the dimension. -/
theorem physical_pair_near_one_decay
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ s < (1 : ℝ),
      Tendsto (fun n : ℕ =>
        (physicalFullOverlapLaw (n := n) (m := 2) μ β :
          Measure (FullOverlapCoordinates 2)) (fullPairCapEvent s))
        atTop (𝓝 0) := by
  let c := mixtureCoefficients μ
  let K := Real.sqrt (spatialVariance c)+1
  have hcov : 0 < covariancePolynomial c 1 := by
    rw [show c = mixtureCoefficients μ from rfl, covariancePolynomial_mixture]
    exact μ.xi_pos (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨a, s, ha, has, hs, hentropy⟩ :=
    exists_entropy_beating_latitude hβ hK
  have hN : Tendsto (fun n : ℕ => ((n+2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hrate : 0 < 1/(2*covariancePolynomial c 1) := by positivity
  have hexp : Tendsto (fun n : ℕ =>
      2*Real.exp (-((n+2 : ℕ) : ℝ)/(2*covariancePolynomial c 1)))
      atTop (𝓝 0) := by
    have hh := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hN.const_mul_atTop hrate)).const_mul 2
    convert hh using 1
    · ext n
      dsimp only [Function.comp_apply]
      congr 1
      ring_nf
    · norm_num
  have hbadBound (n : ℕ) :
      (disorderLaw (n+2) μ.maxDegree).real (physicalFieldGoodSet μ n K)ᶜ ≤
        2*Real.exp (-((n+2 : ℕ) : ℝ)/(2*covariancePolynomial c 1)) := by
    simpa only [K, c, one_pow, one_mul] using
      physicalFieldGoodSet_complement_bound μ n hcov
        (t := 1) (by norm_num)
  have hbad : Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real (physicalFieldGoodSet μ n K)ᶜ)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      hexp
    · exact Filter.Eventually.of_forall (fun n => measureReal_nonneg)
    · exact Filter.Eventually.of_forall hbadBound
  have hreal : Tendsto (fun n : ℕ =>
      (physicalFullOverlapLaw (n := n) (m := 2) μ β :
        Measure (FullOverlapCoordinates 2)).real (fullPairCapEvent s))
      atTop (𝓝 0) := by
    have hupper := hentropy.add hbad
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (by simpa using hupper)
    · exact Filter.Eventually.of_forall (fun n => measureReal_nonneg)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
        physicalFullOverlapLaw_pairCap_real_le_of_goodField
        μ hβ hn (physicalFieldGoodSet μ n K)
        (physicalFieldGoodSet_measurable μ n K)
        (fun J hJ x hx => physicalFieldGoodSet_uniform μ n K J hJ x hx)
        ha has hs
  refine ⟨s, hs, ?_⟩
  exact (ENNReal.tendsto_toReal_zero_iff
    (fun n => measure_ne_top _ _)).mp hreal

end SlowEquilibration.PureCapturePhysicalNearOneDecay
