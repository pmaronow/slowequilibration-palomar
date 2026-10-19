module
public import FourPapersCommon.MixedOutsideGaps
public import Targets.Section5InterleavedScalarContinuity
public import Targets.Section5CompactWitness

@[expose] public section

/-! Compact scalar witnesses for genuine mixed interleaved comparisons.
The trial overlap is frozen at each witness, so compactness crosses half-open
trial boundaries without changing the physical constrained overlap. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set SpinGlass SpinGlass.Targets
namespace FourPapersCommon
set_option maxHeartbeats 900000

 def mixedInterleavedComparisonDeficit (ξ : AdmissibleEvenMixture) {k : ℕ}
    (s : RSBScheme k) (h : ℝ) (r j : ℕ) (v ell : ℝ) (p : ℝ×ℝ) : ℝ :=
    2*parisiF (mixedClockScheme ξ s) (mixedBeta ξ) (k+2) h-
      section5InterleavedScalarV (mixedClockScheme ξ s) (mixedBeta ξ) h r j p.1 (ξ.clock v) ell+
      ell*p.2-p.1*ξ.tangentRemainder p.2 v

 theorem mixedInterleavedComparisonDeficit_at_trial (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (r j : ℕ) (t v : ℝ) :
    mixedInterleavedComparisonDeficit ξ s h r j v 0 (t,v)=
      section5InterleavedScalarDeficit (mixedClockScheme ξ s) (mixedBeta ξ) h r j t (ξ.clock v) := by
  simp [mixedInterleavedComparisonDeficit,section5InterleavedScalarDeficit,tangentRemainder_self]

 theorem continuousOn_mixedInterleavedComparisonDeficit (ξ : AdmissibleEvenMixture)
    {k : ℕ} (s : RSBScheme k) (h : ℝ) (r : ℕ) {j : ℕ} (hj : j ≤ k+1)
    {v : ℝ} (hv : |v| ∈ Icc (s.q (j-1)) (s.q j)) (ell : ℝ)
    {S : Set (ℝ×ℝ)} (hS : ∀p∈S,p.2∈Icc (-1:ℝ) 1) :
    ContinuousOn (mixedInterleavedComparisonDeficit ξ s h r j v ell) S := by
  have HV := (continuousOn_section5InterleavedScalarV_trial (mixedClockScheme ξ s)
    (mixedBeta ξ) h r hj ell).comp
    ((continuous_fst.prodMk continuous_const).continuousOn)
    (show MapsTo (fun p:ℝ×ℝ => (p.1,ξ.clock v)) S
      {z | |z.2|∈Icc ((mixedClockScheme ξ s).q (j-1)) ((mixedClockScheme ξ s).q j)} from
      fun _ _ => clock_mem_abs_interval ξ s hj hv)
  have HR : ContinuousOn (fun p:ℝ×ℝ => ξ.tangentRemainder p.2 v) S := by
    unfold AdmissibleEvenMixture.tangentRemainder
    exact ((ξ.continuousOn_value.comp continuous_snd.continuousOn hS).sub continuousOn_const).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub continuousOn_const))
  unfold mixedInterleavedComparisonDeficit
  exact ((continuousOn_const.sub HV).add (continuousOn_const.mul continuous_snd.continuousOn)).sub
    (continuous_fst.continuousOn.mul HR)

 theorem exists_mixedInterleavedComparison_compact_witnesses
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ) (r : ℕ)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hunit : ∀p∈S,p.2∈Icc (-1:ℝ) 1)
    (hpos : ∀p∈S,∃j,1 ≤ j ∧ j ≤ k+1 ∧ ∃v,|v|∈Icc (s.q (j-1)) (s.q j) ∧
      ∃ell,0 < mixedInterleavedComparisonDeficit ξ s h r j v ell p) :
    ∃delta>(0:ℝ),∀p∈S,∃j,1 ≤ j ∧ j ≤ k+1 ∧ ∃v,|v|∈Icc (s.q (j-1)) (s.q j) ∧
      ∃ell,delta ≤ mixedInterleavedComparisonDeficit ξ s h r j v ell p := by
  let I := Σ j : {j:ℕ // 1 ≤ j ∧ j ≤ k+1},
    {v:ℝ // |v|∈Icc (s.q (j.1-1)) (s.q j.1)}×ℝ
  let f := fun i:I => mixedInterleavedComparisonDeficit ξ s h r i.1.1 i.2.1.1 i.2.2
  have hc (i:I) : ContinuousOn (f i) S :=
    continuousOn_mixedInterleavedComparisonDeficit ξ s h r i.1.2.2 i.2.1.2 i.2.2 hunit
  have hp : ∀p∈S,∃i:I,0<f i p := by
    intro p hp
    obtain ⟨j,hj0,hj,v,hv,ell,H⟩ := hpos p hp
    exact ⟨⟨⟨j,hj0,hj⟩,(⟨v,hv⟩,ell)⟩,H⟩
  obtain ⟨delta,hd,Hd⟩ := exists_uniform_positive_of_compact_witnesses hS f hc hp
  refine ⟨delta,hd,?_⟩
  intro p hp
  obtain ⟨i,hi⟩ := Hd p hp
  exact ⟨i.1.1,i.1.2.1,i.1.2.2,i.2.1.1,i.2.1.2,i.2.2,hi⟩

universe u
 theorem mixed_constrainedPhi_le_interleavedComparison
    {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]
    {n k : ℕ} (hn : 0<n) (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    (sk : MixedDisorder (Ω:=Ω) n ξ) {r j : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    (hj0 : 1 ≤ j) (hj : j ≤ k+1) {t u v ell : ℝ}
    (ht : t∈Icc (0:ℝ) 1) (hv : |v|∈Icc (s.q (j-1)) (s.q j))
    (hatt : ∃σ τ:Config n,overlap n σ τ=u) :
    constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) t u ≤
      2*mixedInterpolationPsi ξ s h t-mixedInterleavedComparisonDeficit ξ s h r j v ell (t,u) := by
  have H := mixed_constrainedPhi_le_interleavedOffDiagonalMajorant hn ξ s h sk hr0 hr hj0 hj (ell:=ell) ht hv hatt
  dsimp [mixedInterpolationPsi,mixedInterleavedComparisonDeficit]
  linarith only [H]

 theorem exists_mixed_constrainedPhi_compact_interleaved_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hunit : ∀p∈S,p.2∈Icc (-1:ℝ) 1)
    (ht : ∀p∈S,p.1∈Icc (0:ℝ) 1)
    (hpos : ∀p∈S,∃j,1 ≤ j ∧ j ≤ k+1 ∧ ∃v,|v|∈Icc (s.q (j-1)) (s.q j) ∧
      ∃ell,0 < mixedInterleavedComparisonDeficit ξ s h r j v ell p) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  obtain ⟨delta,hd,Hd⟩ := exists_mixedInterleavedComparison_compact_witnesses ξ s h r hS hunit hpos
  refine ⟨delta,hd,?_⟩
  intro Ω _ _ p hp n hn sk hatt
  obtain ⟨j,hj0,hj,v,hv,ell,Hell⟩ := Hd p hp
  have HB := mixed_constrainedPhi_le_interleavedComparison hn ξ s h sk hr0 hr hj0 hj (ell:=ell) (ht p hp) hv hatt
  exact HB.trans (by linarith only [Hell])

 theorem exists_mixed_constrainedPhi_compact_paddedInterleaved_gap_all_spaces
    {k : ℕ} (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (h : ℝ)
    {r : ℕ} (hr0 : 1 ≤ r) (hr : r ≤ k+1)
    {S : Set (ℝ×ℝ)} (hS : IsCompact S) (hunit : ∀p∈S,p.2∈Icc (-1:ℝ) 1)
    (ht : ∀p∈S,p.1∈Icc (0:ℝ) 1)
    (hpos : ∀p∈S,∃j,1 ≤ j ∧ j ≤ k+2 ∧ ∃v,|v|∈Icc (s.q (j-1)) (s.q j) ∧
      ∃ell,0 < mixedInterleavedComparisonDeficit ξ s.padOneLast h r j v ell p) :
    ∃delta>(0:ℝ),∀ {Ω : Type u} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)],
      ∀p∈S,∀{n:ℕ},0<n→∀sk:MixedDisorder (Ω:=Ω) n ξ,
      (∃σ τ:Config n,overlap n σ τ=p.2)→
      constrainedPhi n (mixedClockScheme ξ s) (mixedBeta ξ) h sk.U (k+2-r) p.1 p.2 ≤
        2*mixedInterpolationPsi ξ s h p.1-delta := by
  have Hpos : ∀p∈S,∃j,1 ≤ j ∧ j ≤ k+1+1 ∧
      ∃v,|v|∈Icc (s.padOneLast.q (j-1)) (s.padOneLast.q j) ∧
      ∃ell,0 < mixedInterleavedComparisonDeficit ξ s.padOneLast h r j v ell p := by
    intro p hp
    obtain ⟨j,hj0,hj,v,hv,ell,H⟩ := hpos p hp
    exact ⟨j,hj0,by omega,v,by
      simpa only [s.padOneLast_q (p:=j-1) (by omega),s.padOneLast_q hj] using hv,ell,H⟩
  obtain ⟨delta,hd,Hd⟩ := exists_mixed_constrainedPhi_compact_interleaved_gap_all_spaces
    ξ s.padOneLast h hr0 (by omega) hS hunit ht Hpos
  refine ⟨delta,hd,?_⟩
  intro Ω _ _ p hp n hn sk hatt
  have H := Hd (Ω:=Ω) p hp hn sk hatt
  simpa only [mixedClockScheme_padOneLast,show k+1+2-r=(k+2-r)+1 by omega,
    constrainedPhi_padOneLast,mixedInterpolationPsi_padOneLast] using H

end FourPapersCommon
