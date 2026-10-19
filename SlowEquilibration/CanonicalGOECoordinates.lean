-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CorrelatedGOEDeterminants

/-! Literal independent coordinate transport for the canonical GOE provider. -/
@[expose] public section
namespace SlowEquilibration.CanonicalGOECoordinates
noncomputable section
open Function MeasureTheory ProbabilityTheory OAI.MinUncut.GaussianHermite
open CanonicalGOERealization GOEAsymptotics GOEDeterminantMoments GOEScaling OAI.CriticalSK
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def rawPairToHilbert (z : (ι → ℝ)×(κ → ℝ)) : WithLp 2 (EuclideanSpace ℝ ι×EuclideanSpace ℝ κ) :=
  WithLp.toLp 2 (WithLp.toLp 2 z.1,WithLp.toLp 2 z.2)

omit [Fintype ι] [Fintype κ] in
lemma rawPairToHilbert_measurable : Measurable (rawPairToHilbert (ι:=ι) (κ:=κ)) := by
  exact (WithLp.measurable_toLp 2 _).comp
    (((WithLp.measurable_toLp 2 _).comp measurable_fst).prodMk
      ((WithLp.measurable_toLp 2 _).comp measurable_snd))

/-- Standard Hilbert product Gaussian is genuinely the independent raw
coordinate product law, transported through the actual isometric sum split. -/
theorem independent_coordinates_law :
    ((γpi ι).prod (γpi κ)).map (rawPairToHilbert (ι:=ι) (κ:=κ))=
      stdGaussian (WithLp 2 (EuclideanSpace ℝ ι×EuclideanSpace ℝ κ)) := by
  let e : EuclideanSpace ℝ (ι⊕κ) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ ι×EuclideanSpace ℝ κ) :=
    PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : ι⊕κ => ℝ)
  have hc:= (measurePreserving_sumPiEquivProdPi (fun _ : ι⊕κ => gaussianReal 0 1)).map_eq
  have he : (e : EuclideanSpace ℝ (ι⊕κ) → _) ∘ WithLp.toLp 2=
      rawPairToHilbert ∘ MeasurableEquiv.sumPiEquivProdPi (fun _ : ι⊕κ=>ℝ) := rfl
  calc
    _=((γpi (ι⊕κ)).map (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι⊕κ=>ℝ))).map rawPairToHilbert := by rw [hc]
    _=(γpi (ι⊕κ)).map ((e : EuclideanSpace ℝ (ι⊕κ) → _) ∘ WithLp.toLp 2) := by
      rw [Measure.map_map rawPairToHilbert_measurable (MeasurableEquiv.sumPiEquivProdPi _).measurable,← he]
    _=((γpi (ι⊕κ)).map (WithLp.toLp 2)).map e := by
      rw [Measure.map_map e.continuous.measurable (WithLp.measurable_toLp 2 _)]
    _=stdGaussian _ := by rw [map_pi_eq_stdGaussian,stdGaussian_map e]

lemma scaleFactor_goeScale_eq (n : ℕ) {N : ℕ} (hN : 0 < N) {b : ℝ} (hb : 0 ≤ b) :
    scaleFactor n N b*goeScale n=Real.sqrt (2*b/(N:ℝ))/2 := by
  have h1:=scaleFactor_goeScale n hN hb
  have h2 : 2*(Real.sqrt (2*b/(N:ℝ))/2)^2=b/(N:ℝ) := by
    have hs:=Real.sq_sqrt (show 0≤2*b/(N:ℝ) by positivity)
    calc
      _=Real.sqrt (2*b/(N:ℝ))^2/2 := by ring
      _=(2*b/(N:ℝ))/2 := by rw [hs]
      _=b/(N:ℝ) := by ring
  have ha : 0 ≤ scaleFactor n N b*goeScale n := by unfold scaleFactor goeScale;positivity
  have hb' : 0≤Real.sqrt (2*b/(N:ℝ))/2 := by positivity
  nlinarith

/-- Pointwise identity of both canonical GOE constructions, rather than
only equality of their marginal probability laws. -/
theorem canonical_realization_eq_physical (n j : ℕ) {b : ℝ} (hb : 0 ≤ b)
    (z : CorrelatedGOEDeterminants.Coordinates n) :
    gaussianToMatrix (CanonicalGOERealization.realization (n+1) (n+1+j) b (WithLp.toLp 2 z))=
      CorrelatedGOEDeterminants.physicalMatrix n j b z := by
  rw [CanonicalGOERealization.realization_eq]
  dsimp only [Function.comp_apply,CorrelatedGOEDeterminants.physicalMatrix,GOEDeterminantMoments.realization]
  rw [← gaussianToMatrix_scalar,symmetrize_scalar,
    scaleFactor_goeScale_eq n (by omega) hb]

end
end SlowEquilibration.CanonicalGOECoordinates
