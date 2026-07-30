/-
# Two-polynomial common interleaver converse

Compatibility umbrella for the common-interleaver refactor.  The theorem
families formerly in this file now live in `RealRooted.CommonInterleaver.*`,
with the finite-family and Chudnovsky--Seymour packaging in
`RealRooted.CommonInterleaver.PairwiseUpgrade`.
-/
import RealRooted.CommonInterleaver.PairwiseUpgrade

open Polynomial

noncomputable section

namespace RealRooted

theorem compatibleSameDegreePairHasCommonInterleaver :
    CompatibleSameDegreePairHasCommonInterleaverStatement :=
  sorry

theorem compatibleSuccDegreePairHasCommonInterleaver :
    CompatibleSuccDegreePairHasCommonInterleaverStatement :=
  sorry

theorem posComboNatDegreeClose ⦃f g : ℝ[X]⦄ (hfg : PosComboRealRooted f g) :
    f.natDegree ≤ g.natDegree + 1 ∧ g.natDegree ≤ f.natDegree + 1 := by
  sorry

theorem posComboNoCommonOrientation ⦃f g : ℝ[X]⦄
    (hfg : PosComboRealRooted f g)
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r) :
    Prec f g ∨ Prec g f := by
  sorry

theorem posComboNoCommonAffineFamily :
    PosComboNoCommonAffineFamilyStatement :=
  sorry

theorem posComboNoCommonBoundaryRightPairOrientation ⦃f g : ℝ[X]⦄
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg_lo : f.natDegree ≤ g.natDegree)
    (hdeg_hi : g.natDegree ≤ f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    ⦃t : ℝ⦄ (ht : 0 < t) :
    Prec (C t * f + g) (X * f) ∨ Prec (X * f) (C t * f + g) := by
  sorry

theorem posComboNoCommonSameDegreeOrientationAlternativeNonneg :
    PosComboNoCommonSameDegreeOrientationAlternativeNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreePairHasCommonInterleaverNonneg :
    PosComboNoCommonSameDegreePairHasCommonInterleaverNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreePairHasCommonInterleaverNonneg :
    PosComboNoCommonSuccDegreePairHasCommonInterleaverNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeSlotDataNonneg :
    PosComboNoCommonSameDegreeSlotDataNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeRootCrossingNonneg :
    PosComboNoCommonSameDegreeRootCrossingNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeRootCountNonneg :
    PosComboNoCommonSameDegreeRootCountNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeRootCountAboveNonneg :
    PosComboNoCommonSameDegreeRootCountAboveNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeRootCountNonRootNonneg :
    PosComboNoCommonSameDegreeRootCountNonRootNonnegStatement :=
  sorry

theorem posComboNoCommonSameDegreeRootCountAboveNonRootNonneg :
    PosComboNoCommonSameDegreeRootCountAboveNonRootNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeSlotDataNonneg :
    PosComboNoCommonSuccDegreeSlotDataNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCrossingNonneg :
    PosComboNoCommonSuccDegreeRootCrossingNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCountNonneg :
    PosComboNoCommonSuccDegreeRootCountNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCountAboveNonneg :
    PosComboNoCommonSuccDegreeRootCountAboveNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCountAboveNonRootNonneg :
    PosComboNoCommonSuccDegreeRootCountAboveNonRootNonnegStatement :=
  sorry

theorem compatibleSuccDegreeClosedSegmentCountEq :
    CompatibleSuccDegreeClosedSegmentCountEqStatement :=
  sorry

theorem compatibleSuccDegreeEndpointSignLowerCountEq :
    CompatibleSuccDegreeEndpointSignLowerCountEqStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCountNonRootNonneg :
    PosComboNoCommonSuccDegreeRootCountNonRootNonnegStatement :=
  sorry

theorem posComboNoCommonSuccDegreeRootCountResidualPrec ⦃f g : ℝ[X]⦄
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits)
    (hf_zero : f.coeff 0 = 0)
    (hg_ne : g.coeff 0 ≠ 0) :
    Prec f g := by
  sorry

theorem posComboNoCommonSuccDegreeRootCountLeadBothNonzeroNonneg ⦃f g : ℝ[X]⦄
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits)
    (hf_ne : f.coeff 0 ≠ 0)
    (hg_ne : g.coeff 0 ≠ 0)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  sorry

theorem posComboNoCommonSuccDegreeRootCountLeadRightZeroNonneg ⦃f g : ℝ[X]⦄
    (hf_pos : HasPosLeadingCoeff f)
    (hg_pos : HasPosLeadingCoeff g)
    (hfnn : HasNonnegCoeffs f)
    (hgnn : HasNonnegCoeffs g)
    (hfg : PosComboRealRooted f g)
    (hdeg : g.natDegree = f.natDegree + 1)
    (hno : ∀ r, f.IsRoot r → ¬ g.IsRoot r)
    (hf_split : f.Splits)
    (hf_ne : f.coeff 0 ≠ 0)
    (hg_zero : g.coeff 0 = 0)
    (x : ℝ) :
    ((f.roots.filter (· ≤ x)).card : ℤ) - (g.roots.filter (· ≤ x)).card ≤ 0 ∧
    ((g.roots.filter (· ≤ x)).card : ℤ) - (f.roots.filter (· ≤ x)).card ≤ 2 := by
  sorry



end RealRooted
