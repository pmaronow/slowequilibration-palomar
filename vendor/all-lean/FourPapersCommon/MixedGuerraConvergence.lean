module
/- Modified for this distribution (2026): Lean compiler/module compatibility and
   library interface adaptations. Existing source notices are retained. -/
public import FourPapersCommon.MixedGuerraBounds
public import FourPapersCommon.MixtureCoercivity
public import Targets.TalagrandConvergence
public import Targets.ReplicaMeasure

@[expose] public section

/-! The mixed-model interpolation gap and its physical-overlap tail control.

The elementary cascade and endpoint-safe Grönwall arguments are adapted from
`Targets.TalagrandConvergence` (Apache 2.0). The covariance is genuinely mixed:
the remainder is the convex tangent error of ξ at the original physical q.
The variance clock changes the Gaussian recursion, not the physical overlap.
Overlap concentration remains an explicit input to the convergence deduction.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open SpinGlass SpinGlass.Targets
open scoped BigOperators NNReal
namespace FourPapersCommon
universe u
variable {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
set_option maxHeartbeats 800000

def mixedInterpolationPsi (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h t : ℝ) : ℝ :=
  Real.log 2 + parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h -
    t * mixedSchemeCorrection ξ s

def mixedInterpolationGap {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) (t : ℝ) : ℝ :=
  mixedInterpolationPsi ξ s h t - guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h U t

theorem mixedInterpolationGap_zero {n : ℕ} (hn : 0 < n) (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (U : Ω → EnergySpace n) :
    mixedInterpolationGap ξ s h U 0 = 0 := by
  simp [mixedInterpolationGap, mixedInterpolationPsi,
    guerraPhi_zero n hn (mixedClockScheme ξ s) (mixedBeta ξ) h U]

theorem continuousOn_mixedInterpolationGap {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ) :
    ContinuousOn (mixedInterpolationGap ξ s h sk.U) (Icc (0 : ℝ) 1) := by
  have hψ : Continuous (mixedInterpolationPsi ξ s h) := by
    unfold mixedInterpolationPsi
    fun_prop
  exact hψ.continuousOn.sub
    (mixed_continuousOn_guerraPhi (mixedBeta ξ) h sk.U sk.hU (mixedClockScheme ξ s))

theorem hasDerivAt_mixedInterpolationGap {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (mixedInterpolationGap ξ s h sk.U)
      (mixedGuerraRemainder ξ s h sk.U t) t := by
  have hφ := (mixed_guerra_identity hn ξ sk s h).2.2 t ht
  have hψ : HasDerivAt (mixedInterpolationPsi ξ s h) (-mixedSchemeCorrection ξ s) t := by
    convert! (hasDerivAt_const t (Real.log 2 +
      parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k + 2) h)).sub
      ((hasDerivAt_id t).mul_const (mixedSchemeCorrection ξ s)) using 1
    simp
  convert! hψ.sub hφ using 1
  simp

theorem mixedInterpolationGap_nonneg {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ mixedInterpolationGap ξ s h sk.U t := by
  have hm : MonotoneOn (mixedInterpolationGap ξ s h sk.U) (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
      (continuousOn_mixedInterpolationGap ξ sk s h)
    · rw [interior_Icc]
      intro x hx
      exact (hasDerivAt_mixedInterpolationGap hn ξ sk s h hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      rw [(hasDerivAt_mixedInterpolationGap hn ξ sk s h hx).deriv]
      exact mixedGuerraRemainder_nonneg hn ξ s h sk.U x
  have hh := hm (by simp) ht ht.1
  simpa only [mixedInterpolationGap_zero hn ξ s h sk.U] using hh

/-- Grönwall comparison differentiates only in the open interval; the genuine
square-root interpolation endpoints are handled by continuity. -/
theorem mixedInterpolationGap_le_mul_exp {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t₀ K ε : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hbound : ∀ x ∈ Ioo (0 : ℝ) t₀,
      mixedGuerraRemainder ξ s h sk.U x ≤ K * mixedInterpolationGap ξ s h sk.U x + ε)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) t₀) :
    mixedInterpolationGap ξ s h sk.U t ≤ ε * Real.exp ((K + 1) * t) := by
  let f := mixedInterpolationGap ξ s h sk.U
  let g : ℝ → ℝ := fun x => Real.exp (-(K + 1) * x) * (f x + ε)
  have hsub : Icc (0 : ℝ) t₀ ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨hx.1, hx.2.trans ht₀.2⟩
  have hf : ContinuousOn f (Icc (0 : ℝ) t₀) :=
    (continuousOn_mixedInterpolationGap ξ sk s h).mono hsub
  have hg : ContinuousOn g (Icc (0 : ℝ) t₀) :=
    (by fun_prop : Continuous (fun x : ℝ => Real.exp (-(K + 1) * x))).continuousOn.mul
      (hf.add continuousOn_const)
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) t₀,
      HasDerivAt g (Real.exp (-(K + 1) * x) *
        (mixedGuerraRemainder ξ s h sk.U x - (K + 1) * (f x + ε))) x := by
    intro x hx
    have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1, hx.2.trans_le ht₀.2⟩
    convert! (((hasDerivAt_id x).const_mul (-(K + 1))).exp).mul
      ((hasDerivAt_mixedInterpolationGap hn ξ sk s h hx1).add_const ε) using 1
    dsimp only [f, id_eq]
    ring
  have hsign : ∀ x ∈ Ioo (0 : ℝ) t₀,
      Real.exp (-(K + 1) * x) *
        (mixedGuerraRemainder ξ s h sk.U x - (K + 1) * (f x + ε)) ≤ 0 := by
    intro x hx
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hfn := mixedInterpolationGap_nonneg hn ξ sk s h (hsub ⟨hx.1.le, hx.2.le⟩)
    have hb := hbound x hx
    change mixedGuerraRemainder ξ s h sk.U x - (K + 1) *
      (mixedInterpolationGap ξ s h sk.U x + ε) ≤ 0
    nlinarith [mul_nonneg hK hε]
  have hm : AntitoneOn g (Icc (0 : ℝ) t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hg
    · rw [interior_Icc]
      exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      exact fun x hx => by rw [(hderiv x hx).deriv]; exact hsign x hx
  have hb : Real.exp (-(K + 1) * t) * (f t + ε) ≤ ε := by
    have hh := hm (show (0 : ℝ) ∈ Icc (0 : ℝ) t₀ from ⟨le_rfl, ht₀.1⟩) ht ht.1
    simpa only [g, f, mixedInterpolationGap_zero hn ξ s h sk.U, mul_zero,
      Real.exp_zero, zero_add, one_mul] using hh
  calc
    f t ≤ f t + ε := le_add_of_nonneg_right hε
    _ = Real.exp ((K + 1) * t) * (Real.exp (-(K + 1) * t) * (f t + ε)) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ ≤ Real.exp ((K + 1) * t) * ε := mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ε * Real.exp ((K + 1) * t) := mul_comm _ _

/-- Monotonicity of genuine bounded cascade observables, requiring Gaussian
integrability but no specialized SK covariance. -/
theorem mixed_guerraReplicaExpectation_mono {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {F G : ℕ → Config n → Config n → ℝ} {C D : ℝ}
    (hF : ∀ j σ τ, |F j σ τ| ≤ C) (hG : ∀ j σ τ, |G j σ τ| ≤ D)
    (hle : ∀ j σ τ, F j σ τ ≤ G j σ τ) :
    guerraReplicaExpectation n s (mixedBeta ξ) h sk.U t F ≤
      guerraReplicaExpectation n s (mixedBeta ξ) h sk.U t G :=
  integral_mono
    (mixed_integrable_guerraReplicaAccum (mixedBeta ξ) h sk.U sk.hU s ht hF (k + 2) 0)
    (mixed_integrable_guerraReplicaAccum (mixedBeta ξ) h sk.U sk.hU s ht hG (k + 2) 0)
    (fun ω => guerraReplicaAccum_mono n s (mixedBeta ξ) (sk.U ω) h ht hF hG hle (k + 2) 0)

theorem mixed_guerraReplicaExpectation_const_add_mul {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (a b : ℝ)
    {F : ℕ → Config n → Config n → ℝ} {C : ℝ} (hF : ∀ j σ τ, |F j σ τ| ≤ C) :
    guerraReplicaExpectation n s (mixedBeta ξ) h sk.U t (fun j σ τ => a + b * F j σ τ) =
      a + b * guerraReplicaExpectation n s (mixedBeta ξ) h sk.U t F := by
  let Fs : Fin 2 → ℕ → Config n → Config n → ℝ := ![fun _ _ _ => 1, F]
  have hb : ∀ (i : Fin 2) l σ τ, |Fs i l σ τ| ≤ (![1, C] i) := by
    intro i l σ τ
    fin_cases i
    · norm_num [Fs]
    · exact hF l σ τ
  have hp : ∀ U : EnergySpace n,
      guerraReplicaAccum n s (mixedBeta ξ) U h t (fun l σ τ => a + b * F l σ τ) (k + 2) 0 =
        a + b * guerraReplicaAccum n s (mixedBeta ξ) U h t F (k + 2) 0 := by
    intro U
    have hh := guerraReplicaAccum_sum_mul n s (mixedBeta ξ) U h ht ![a, b] Fs ![1, C] hb (k + 2) 0
    simpa [Fs, Fin.sum_univ_succ, guerraReplicaAccum_const n s (mixedBeta ξ) U h ht,
      guerraMass_top] using hh
  unfold guerraReplicaExpectation
  simp_rw [hp]
  rw [integral_add (integrable_const a)
    ((mixed_integrable_guerraReplicaAccum (mixedBeta ξ) h sk.U sk.hU s ht hF (k + 2) 0).const_mul b),
    integral_const_mul]
  simp

/-- The averaging recursion uses the variance clock. The tail center is the
original physical overlap level s.q, including negative attainable overlaps. -/
def mixedOverlapTail {n : ℕ} (ξ : AdmissibleEvenMixture) {k : ℕ} (s : RSBScheme k)
    (h : ℝ) (U : Ω → EnergySpace n) (t a : ℝ) : ℝ := by
  classical
  exact guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h U t
    (fun j σ τ => if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0)

theorem mixedOverlapTail_mem_Icc {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (a : ℝ) :
    mixedOverlapTail ξ s h sk.U t a ∈ Icc (0 : ℝ) 1 := by
  classical
  let F : ℕ → Config n → Config n → ℝ := fun j σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0
  have hb : ∀ j σ τ, |F j σ τ| ≤ 1 := by
    intro j σ τ
    dsimp [F]
    split_ifs <;> norm_num
  change 0 ≤ guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t F ∧
    guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t F ≤ 1
  refine ⟨guerraReplicaExpectation_nonneg n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U ht
    (fun j σ τ => ?_), ?_⟩
  · dsimp [F]
    split_ifs <;> norm_num
  · have hh := mixed_guerraReplicaExpectation_mono ξ sk (mixedClockScheme ξ s) h ht hb
      (G := fun _ _ _ => 1) (C := 1) (D := 1) (by intros; norm_num)
      (fun j σ τ => (le_abs_self _).trans (hb j σ τ))
    simpa only [guerraReplicaExpectation_const n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U ht 1] using hh

/-- The genuine mixed tangent error is bounded by a second-derivative constant
and the physical squared-overlap tail; all comparison integrals are integrable. -/
theorem mixedGuerraRemainder_le_of_overlapTail {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a δ : ℝ} (ha : 0 ≤ a) (htail : mixedOverlapTail ξ s h sk.U t a ≤ δ) :
    mixedGuerraRemainder ξ s h sk.U t ≤ (ξ.second 1 / 2) * (a + 4 * δ) := by
  classical
  let F : ℕ → Config n → Config n → ℝ := fun j σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - j)) ^ 2 then 1 else 0
  have hF : ∀ j σ τ, |F j σ τ| ≤ 1 := by
    intro j σ τ
    dsimp [F]
    split_ifs <;> norm_num
  have hG : ∀ j σ τ, |a + 4 * F j σ τ| ≤ a + 4 := by
    intro j σ τ
    calc
      _ ≤ |a| + |4 * F j σ τ| := abs_add_le _ _
      _ ≤ a + 4 := by
        rw [abs_of_nonneg ha, abs_mul, show |(4 : ℝ)| = 4 by norm_num]
        linarith [hF j σ τ]
  have hsq : ∀ j σ τ, (overlap n σ τ - s.q (k + 2 - j)) ^ 2 ≤ a + 4 * F j σ τ := by
    intro j σ τ
    have hs := (le_abs_self _).trans (guerra_overlap_sq_le_four hn s j σ τ)
    dsimp [F]
    split_ifs with he
    · linarith
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge he).le
  let R : ℕ → Config n → Config n → ℝ := fun j σ τ =>
    ξ.tangentRemainder (overlap n σ τ) (s.q (k + 2 - j))
  have hR : ∀ j σ τ, |R j σ τ| ≤ 2 * (ξ.value 1 + ξ.variance) := by
    intro j σ τ
    exact abs_tangentRemainder_bound ξ (abs_overlap_le_one hn σ τ) (by
      rw [abs_of_nonneg (s.q_nonneg (by omega))]
      exact s.q_le_one (by omega))
  have hRG : ∀ j σ τ, R j σ τ ≤ ξ.second 1 * (a + 4 * F j σ τ) := by
    intro j σ τ
    exact (ξ.tangentRemainder_quadratic_upper
      (abs_le.mp (abs_overlap_le_one hn σ τ))
      ⟨by linarith [s.q_nonneg (p := k + 2 - j) (by omega)], s.q_le_one (by omega)⟩).trans
      (mul_le_mul_of_nonneg_left (hsq j σ τ) (ξ.second_nonneg 1))
  have hGG : ∀ j σ τ, |ξ.second 1 * (a + 4 * F j σ τ)| ≤ ξ.second 1 * (a + 4) := by
    intro j σ τ
    rw [abs_mul, abs_of_nonneg (ξ.second_nonneg 1)]
    exact mul_le_mul_of_nonneg_left (hG j σ τ) (ξ.second_nonneg 1)
  have he := mixed_guerraReplicaExpectation_mono ξ sk (mixedClockScheme ξ s) h ht hR hGG hRG
  have hlin := mixed_guerraReplicaExpectation_const_add_mul ξ sk (mixedClockScheme ξ s) h ht
    (ξ.second 1 * a) (4 * ξ.second 1) hF
  have hfun : (fun j σ τ => ξ.second 1 * (a + 4 * F j σ τ)) =
      (fun j σ τ => ξ.second 1 * a + (4 * ξ.second 1) * F j σ τ) := by
    funext j σ τ
    ring
  rw [hfun, hlin] at he
  change guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t F ≤ δ at htail
  unfold mixedGuerraRemainder
  rw [ite_eq_left ht]
  change (1 / 2) * guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t R ≤ _
  have hc := ξ.second_nonneg 1
  nlinarith [mul_le_mul_of_nonneg_left htail (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hc)]

theorem mixedGuerraRemainder_le_of_overlap_concentration {n : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (sk : MixedDisorder (Ω := Ω) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {K η : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η)
    (htail : mixedOverlapTail ξ s h sk.U t (K * mixedInterpolationGap ξ s h sk.U t + η) ≤ η) :
    mixedGuerraRemainder ξ s h sk.U t ≤
      ((ξ.second 1 / 2) * K) * mixedInterpolationGap ξ s h sk.U t + (5 * ξ.second 1 / 2) * η := by
  have ha := add_nonneg (mul_nonneg hK (mixedInterpolationGap_nonneg hn ξ sk s h ⟨ht.1.le, ht.2.le⟩)) hη
  have hh := mixedGuerraRemainder_le_of_overlapTail hn ξ sk s h ht ha htail
  nlinarith only [hh]


/-- The final cascade tail is a convex combination of genuine level replica
laws, with original physical centers. A zero first depth has zero weight. -/
theorem mixedOverlapTail_le_of_replicaMeasure {n : ℕ} (ξ : AdmissibleEvenMixture)
    (sk : MixedDisorder (Ω := Ω) n ξ) {k : ℕ} (s : RSBScheme k) (h : ℝ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {a δ : ℝ}
    (hbound : ∀ d, 1 ≤ d → d ≤ k + 1 →
      guerraReplicaMeasure n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t d
        (fun σ τ => if a ≤ (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0) ≤ δ) :
    mixedOverlapTail ξ s h sk.U t a ≤ δ := by
  classical
  let K : ℕ → Config n → Config n → ℝ := fun d σ τ =>
    if a ≤ (overlap n σ τ - s.q (k + 2 - d)) ^ 2 then 1 else 0
  have hK : ∀ d σ τ, |K d σ τ| ≤ 1 := by intros; dsimp [K]; split_ifs <;> norm_num
  change guerraReplicaExpectation n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U t K ≤ δ
  rw [guerraReplicaExpectation_eq_sum_measures (mixedClockScheme ξ s) (mixedBeta ξ) h
    sk.hU.repr_measurable ht hK]
  calc
    _ ≤ ∑ d ∈ Finset.range (k + 2),
        (guerraMass (mixedClockScheme ξ s) d - guerraMass (mixedClockScheme ξ s) (d + 1)) * δ := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0, guerraMass, s.m_top]
      · exact mul_le_mul_of_nonneg_left (hbound d (by omega) (by
          have := Finset.mem_range.mp hd; omega))
          (guerraMass_drop_nonneg (mixedClockScheme ξ s) d)
    _ = δ := by
      rw [← Finset.sum_mul, guerraMass_sum_drops, guerraMass_top]
      ring

/-- The endpoint-safe deduction also permits a different genuine Gaussian
probability space at each system size. -/
theorem mixedInterpolation_uniform_of_remainder_control
    (Ωn : ℕ → Type u) [∀ n, MeasureSpace (Ωn n)]
    [∀ n, IsProbabilityMeasure (ℙ : Measure (Ωn n))]
    (ξ : AdmissibleEvenMixture) (sk : ∀ n, MixedDisorder (Ω := Ωn n) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t₀ K : ℝ}
    (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (hK : 0 ≤ K)
    (hcontrol : ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      mixedGuerraRemainder ξ s h (sk n).U t ≤
        K * mixedInterpolationGap ξ s h (sk n).U t + δ) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) t₀,
      |guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U t -
        mixedInterpolationPsi ξ s h t| < ε := by
  intro ε hε
  let E := Real.exp ((K + 1) * t₀)
  let δ := ε / (E + 1)
  have hE : 0 < E := Real.exp_pos _
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hδε : δ * E < ε := by
    have he : δ * (E + 1) = ε := div_mul_cancel₀ ε (by positivity : E + 1 ≠ 0)
    nlinarith
  filter_upwards [hcontrol δ hδ, eventually_gt_atTop 0] with n hn hpos
  intro t ht
  have hgap := mixedInterpolationGap_nonneg hpos ξ (sk n) s h ⟨ht.1, ht.2.trans ht₀.2⟩
  have habs : |guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U t -
      mixedInterpolationPsi ξ s h t| = mixedInterpolationGap ξ s h (sk n).U t := by
    rw [abs_sub_comm, ← mixedInterpolationGap, abs_of_nonneg hgap]
  rw [habs]
  have hle := mixedInterpolationGap_le_mul_exp hpos ξ (sk n) s h ht₀ hK hδ.le hn ht
  have hexp : Real.exp ((K + 1) * t) ≤ E :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by positivity))
  exact (hle.trans (mul_le_mul_of_nonneg_left hexp hδ.le)).trans_lt hδε

theorem mixedInterpolation_uniform_of_overlap_concentration
    (Ωn : ℕ → Type u) [∀ n, MeasureSpace (Ωn n)]
    [∀ n, IsProbabilityMeasure (ℙ : Measure (Ωn n))]
    (ξ : AdmissibleEvenMixture) (sk : ∀ n, MixedDisorder (Ω := Ωn n) n ξ)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) {t₀ K : ℝ}
    (ht₀ : t₀ ∈ Ico (0 : ℝ) 1) (hK : 0 ≤ K)
    (hconcentration : ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Ioo (0 : ℝ) t₀,
      mixedOverlapTail ξ s h (sk n).U t
        (K * mixedInterpolationGap ξ s h (sk n).U t + η) ≤ η) :
    ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) t₀,
      |guerraPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h (sk n).U t -
        mixedInterpolationPsi ξ s h t| < ε := by
  have hc := ξ.second_nonneg 1
  apply mixedInterpolation_uniform_of_remainder_control Ωn ξ sk s h ⟨ht₀.1, ht₀.2.le⟩
    (K := (ξ.second 1 / 2) * K) (mul_nonneg (by positivity) hK)
  intro δ hδ
  let L := 5 * ξ.second 1 / 2
  let η := δ / (L + 1)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hη : 0 < η := div_pos hδ (by positivity)
  have hsmall : L * η ≤ δ := by
    have he : η * (L + 1) = δ := div_mul_cancel₀ δ (by positivity : L + 1 ≠ 0)
    nlinarith
  filter_upwards [hconcentration η hη, eventually_gt_atTop 0] with n hn hpos
  intro t ht
  have ht1 : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, ht.2.trans ht₀.2⟩
  have hh := mixedGuerraRemainder_le_of_overlap_concentration hpos ξ (sk n) s h ht1 hK hη.le (hn t ht)
  exact hh.trans (add_le_add le_rfl hsmall)

end FourPapersCommon
