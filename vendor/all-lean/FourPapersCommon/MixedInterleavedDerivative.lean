module
public import FourPapersCommon.MixedInterleavedCovariance

@[expose] public section

/-! Genuine simultaneous disorder/variance differentiation of the tagged path
with an arbitrary mixed Gaussian Hamiltonian. Auxiliary variances are explicit. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter Topology SpinGlass SpinGlass.Targets
open PhysLean.Probability.GaussianIBP
open scoped BigOperators
namespace FourPapersCommon
variable {n k : ℕ} {Ω : Type*} [MeasureSpace Ω]
variable [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

noncomputable def mixedInterleavedInterpolationOffDiagonalDerivative
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (β h : ℝ) (sk : MixedDisorder (Ω := Ω) n ξ)
    (r j : ℕ) (hj : j ≤ k + 1) (t u v w : ℝ) : ℝ :=
  ∫ ω, (1 / (n : ℝ)) *
    (t / 2 * (∑ i : sk.hU.ι,
      ((sk.hU.τ i : ℝ) *
        mixedConstrainedSecond (section5ReverseMode s r j (decide (v < 0)))
          (section5ReverseMass s r j)
          (fun l => section5ReversePathVariance s β t v r j l w)
          (2 * k + 4 + 1) (Real.sqrt (w * t) • sk.U ω)
          (sk.hU.w i) (sk.hU.w i) u (fun _ => h) (fun _ => h))) -
      t * ∑ l : Fin (2 * k + 4 + 1),
        (β ^ 2 *
          (section5InterleavedRho s r j |v|
            (2 * k + 4 - l + 1) -
            section5InterleavedRho s r j |v| (2 * k + 4 - l))) *
        mixedLevelVarianceD (Real.sqrt (w * t) • sk.U ω) u
          (section5ReverseMode s r j (decide (v < 0)))
          (section5ReverseMass s r j)
          (fun i => section5ReversePathVariance s β t v r j i w)
          (l : ℕ) (2 * k + 4 + 1 - ((l : ℕ) + 1))
          (section5ReversePathVariance s β t v r j (l : ℕ) w)
          (fun _ => h) (fun _ => h))

/- The derivative is the same genuine mixed replica expression as in the
diagonal construction, but with the covariance square completed at `(u,v)`.
The proof below is the existing finite-cascade differentiation argument with
the two overlap parameters kept distinct. -/
theorem hasDerivAt_section5InterleavedInterpolationOffDiagonal_mixed
    (hn : 0 < n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (β h : ℝ)
    (sk : MixedDisorder (Ω := Ω) n ξ) (r : ℕ) {j : ℕ}
    (hj0 : 1 ≤ j) (hj : j ≤ k + 1) {t u v w : ℝ}
    (ht : t ∈ Set.Icc 0 1)
    (hv : |v| ∈ Set.Icc (s.q (j - 1)) (s.q j))
    (hw : w ∈ Set.Ioo 0 1) [Nonempty (AT.ConstrainedPair n u)] :
    HasDerivAt
      (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v)
      (mixedInterleavedInterpolationOffDiagonalDerivative ξ s β h sk r j hj t u v w) w := by
  let N := 2 * k + 4 + 1
  let mode := section5ReverseMode s r j (decide (v < 0))
  let m := section5ReverseMass s r j
  let path := section5ReversePathVariance s β t v r j
  let ρ := section5InterleavedRho s r j |v|
  let a := fun l => β ^ 2 * (ρ (2 * k + 4 - l + 1) - ρ (2 * k + 4 - l))
  let Z := fun ω => Real.sqrt (w * t) • sk.U ω
  let R := fun ω => ∑ i : sk.hU.ι, (sk.hU.τ i : ℝ) *
    mixedConstrainedSecond mode m (fun l => path l w) N (Z ω)
      (sk.hU.w i) (sk.hU.w i) u (fun _ => h) (fun _ => h)
  let D := fun l : Fin N => fun ω => mixedLevelVarianceD (Z ω) u mode m
    (fun i => path i w) l (N - (l + 1)) (path l w) (fun _ => h) (fun _ => h)
  have hm : ∀ l, 0 ≤ m l := section5ReverseMass_nonneg s r hj
  have hv0 : ∀ l, 0 ≤ path l w := by
    intro l
    exact section5ReversePathVariance_nonneg s β ht hw.2.le r hj hv l
  have hpath (l : ℕ) (_hl : l < N) : HasDerivAt (path l)
      (-(t * a l)) w := by
    change HasDerivAt (fun z => section5TaggedPathVariance s β t |v| j z
      (section5ReverseTag s r j l)) (-(t * a l)) w
    have H := hasDerivAt_section5TaggedPathVariance s β t |v| r hj
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ w
    simpa only [path, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc] using H
  have hpathn : ∀ᶠ z in 𝓝 w, ∀ l, 0 ≤ path l z := by
    filter_upwards [Ioo_mem_nhds hw.1 hw.2] with z hz
    exact section5ReversePathVariance_nonneg s β ht hz.2.le r hj hv
  have hpathf (l : ℕ) (_hl : l < N) : 0 < path l w ∨
      (path l =ᶠ[𝓝 w] fun _ => 0) := by
    rcases section5TaggedPathVariance_pos_or_eq_zero s β ht hj hv hw.2
      (section5ReverseTag s r j l) with hp | hz
    · exact Or.inl hp
    · exact Or.inr (Eventually.of_forall hz)
  have H := (hasDerivAt_mixedConstrainedGaussian_path_trace sk.hU
    (fun z => Real.sqrt (z * t)) u mode m path hm N
    (hasDerivAt_sqrt_mul_time ht.1 hw.1) hpath hpathn hpathf
    (fun _ => h) (fun _ => h)).const_mul (1 / (n : ℝ))
  have he (l : Fin N) : -(t * a l) *
      (if 0 < path l w then ∫ ω, D l ω else 0) =
      -(t * (a l * ∫ ω, D l ω)) := by
    have HH := section5TaggedPathVelocity_mul_ite s β r ht hj hv hw.2
      ⟨(k + 2) + (k + 3) - 1 - l, by omega⟩ (∫ ω, D l ω)
    simpa only [path, section5ReversePathVariance, section5ReverseTag,
      show (k + 2) + (k + 3) - 1 = 2 * k + 4 by omega, a, ρ, mul_assoc, neg_mul] using HH
  have hZ : Measurable Z := sk.hU.repr_measurable.const_smul (Real.sqrt (w * t))
  have hiR : Integrable R := integrable_mixedConstrainedSecond_mixed_trace hn ξ sk hZ
    u mode m (fun l => path l w) hm hv0 N (fun _ => h) (fun _ => h)
  have hiD (l : Fin N) : Integrable (D l) := integrable_mixedLevelVarianceD_all_variances hn hZ
    u mode m (fun i => path i w) hm hv0 l (N - (l + 1)) (fun _ => h) (fun _ => h)
  have hiS : Integrable (fun ω => ∑ l : Fin N, a l * D l ω) :=
    integrable_finsetSum _ fun l _ => (hiD l).const_mul (a l)
  have hlin : (∫ ω, (1 / (n : ℝ)) * (t / 2 * R ω -
      t * ∑ l : Fin N, a l * D l ω)) =
      (1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) -
        t * ∑ l : Fin N, a l * ∫ ω, D l ω) := by
    rw [integral_const_mul, integral_sub (hiR.const_mul _) (hiS.const_mul _),
      integral_const_mul, integral_const_mul,
      integral_finsetSum _ (fun l _ => (hiD l).const_mul (a l))]
    simp_rw [integral_const_mul]
  have hf : (fun z => (1 / (n : ℝ)) * ∫ ω, mixedVectorCascade n mode m
      (fun l => path l z) (constrainedPairFieldBase n
        (Real.sqrt (z * t) • sk.U ω) u) N (fun _ => h) (fun _ => h)) =
      (section5InterleavedInterpolationOffDiagonal n s β h sk.U r j t u v) := by
    funext z
    simpa only [N, mode, m, path,
      show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega] using
      (section5InterleavedInterpolationOffDiagonal_eq_reverse n s β h sk.U r j t u v z).symm
  have hsqrt : t / (2 * Real.sqrt (w * t)) * Real.sqrt (w * t) = t / 2 := by
    by_cases hz : t = 0
    · simp [hz]
    · have hs : Real.sqrt (w * t) ≠ 0 :=
        (Real.sqrt_pos.mpr (mul_pos hw.1 (lt_of_le_of_ne ht.1 (Ne.symm hz)))).ne'
      field_simp [hs]
      have hs' : Real.sqrt (t * w) ≠ 0 := by simpa only [mul_comm] using hs
      exact mul_inv_cancel₀ hs'
  rw [hf, hsqrt] at H
  change HasDerivAt _ ((1 / (n : ℝ)) * (t / 2 * (∫ ω, R ω) +
    ∑ l : Fin N, -(t * a l) * (if 0 < path l w then ∫ ω, D l ω else 0))) w at H
  simp_rw [he] at H
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum, ← sub_eq_add_neg] at H
  apply H.congr_deriv
  rw [← hlin]
  simp only [mixedInterleavedInterpolationOffDiagonalDerivative, R, D, a, mode, m,
    path, ρ, N, Z, show 2 * k + 4 + 1 = (k + 2) + (k + 3) by omega]

end FourPapersCommon
