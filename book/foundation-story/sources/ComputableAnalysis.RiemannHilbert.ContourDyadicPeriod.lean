import ComputableAnalysis.RiemannHilbert.ContourReciprocalAssembly
import ComputableAnalysis.RiemannHilbert.ContourInnerResidue

/-! The actual reciprocal quadrature has a certified geometric error and
converges to the independent geometric circle value of the period. -/
namespace ComputableAnalysis.RiemannHilbert.RectangularContour
open ComplexRaw FunctionTheory DomainFunctions PDE.CauchyContour
set_option autoImplicit false

def uniformContourCell (M j : Nat) : TaggedCell :=
  ⟨(j:Rat)/(M:Rat),((j+1:Nat):Rat)/(M:Rat),squareMidpointParameter M j⟩

theorem uniformContourCell_width (M j : Nat) :
    (uniformContourCell M j).right-(uniformContourCell M j).left=1/(M:Rat) := by
  simp only [uniformContourCell,Rat.natCast_add,Rat.div_def]
  change ((j:Rat)+1)*(M:Rat)⁻¹-(j:Rat)*(M:Rat)⁻¹=1*(M:Rat)⁻¹
  grind only

theorem stageCells_uniform (n : Nat) :
    stageCells n=(List.range (2^n)).map (uniformContourCell (2^n)) := by
  unfold stageCells
  rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform]
  simp only [midpointCells,List.map_map]
  congr 1
  funext j
  change (⟨_,_,_⟩ : TaggedCell)=⟨_,_,squareMidpointParameter (2^n) j⟩
  congr 1
  simp only [squareMidpointParameter,Nat.succ_eq_add_one,Rat.natCast_add,Rat.div_def]
  change ((j:Rat)*((2^n:Nat):Rat)⁻¹+((j:Rat)+1)*((2^n:Nat):Rat)⁻¹)*(2:Rat)⁻¹=
    ((j:Rat)+1*(2:Rat)⁻¹)*((2^n:Nat):Rat)⁻¹
  grind only

theorem contourTaggedSum_append (cs ds : List TaggedCell) :
    taggedSum (cs++ds)=QComplex.add (taggedSum cs) (taggedSum ds) := by
  induction cs with
  | nil => exact (QComplex.zero_add_cert _).symm
  | cons c cs ih =>
    simp only [List.cons_append,taggedSum,ih]
    exact (QComplex.add_assoc_cert _ _ _).symm

theorem uniformContourSum (M count : Nat) :
    taggedSum ((List.range count).map (uniformContourCell M))=
      rationalGridSum count (fun j => QComplex.scaleRat (1/(M:Rat))
        (density (squareMidpointParameter M j))) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [List.range_succ,List.map_append,contourTaggedSum_append,ih]
    simp only [List.map_cons,List.map_nil,taggedSum,uniformContourCell_width,QComplex.add_zero_cert]
    rfl

theorem reciprocalInnerPrefix_stageSum (R : QPos) (n : Nat) :
    reciprocalInnerPrefix R (2^n) ≈ rationalRectangleScalar (taggedSum (stageCells n)) := by
  rw [stageCells_uniform,uniformContourSum]
  exact reciprocalInnerPrefix_rational R (2^n) (Nat.two_pow_pos n)

def rectangularPeriod : Scalar := ⟨PDE.CauchyContour.raw,PDE.CauchyContour.raw_valid⟩
def geometricPeriod : Scalar := ⟨twoPiI,twoPiI_valid⟩

theorem rectangularPeriod_geometric : rectangularPeriod ≈ geometricPeriod := raw_equiv_twoPiI

theorem reciprocalInnerPrefix_error (R : QPos) (n : Nat) :
    Small (sub (reciprocalInnerPrefix R (2^n)).val rectangularPeriod.val)
      (16/((2^n:Nat):Rat)) := by
  have hpos : 0<(16:Rat)/((2^n:Nat):Rat) := by
    rw [Rat.div_def]
    exact Rat.mul_pos (by decide +kernel) (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.two_pow_pos n)))
  have hb := BoxApproximation.point_error rectangularPeriod n (taggedSum (stageCells n))
    (16/((2^n:Nat):Rat)) (Rat.le_of_lt hpos) (raw_encloses_stageSum n)
    (by change (raw.compute n).width≤_; rw [raw_width_zero]; exact Rat.le_of_lt hpos) (raw_height_geometric n)
  have hs := RepresentedCauchySum.small_sub_symm _ _ _ hb
  exact Small.congr (sub_valid (ofQComplex_valid _) rectangularPeriod.property)
    (sub_valid (reciprocalInnerPrefix R (2^n)).property rectangularPeriod.property)
    (add_equiv (equiv_symm (reciprocalInnerPrefix_stageSum R n))
      (equiv_refl _ (neg_valid rectangularPeriod.property))) hs

theorem reciprocalInnerPrefix_converges (radii : Nat → QPos) :
    Converges (fun n => reciprocalInnerPrefix (radii n) (2^n)) rectangularPeriod := by
  intro eps
  refine ⟨RationalMajorant.natRateStage 16 eps, ?_⟩
  intro n hn
  have hp := two_pow_half_pow n
  have he : (16:Rat)/((2^n:Nat):Rat)=16*((1:Rat)/2)^n := by
    have hi := Rat.mul_inv_cancel ((2^n:Nat):Rat) (Rat.ne_of_gt (Rat.natCast_pos.mpr (Nat.two_pow_pos n)))
    simp only [Rat.div_def]
    grind only
  have hb := Rat.mul_le_mul_of_nonneg_left (RationalMajorant.half_pow_le_one_div_succ n)
    (show (0:Rat)≤16 by decide +kernel)
  have hr := RationalMajorant.natRateStage_spec_of_le (show (0:Rat)≤16 by decide +kernel) eps hn
  have hrate : (16:Rat)/((2^n:Nat):Rat)≤eps.val := by
    rw [he]
    have hi : 16*(1/((n+1:Nat):Rat))=16/((n+1:Nat):Rat) := by simp only [Rat.div_def,Rat.one_mul]
    rw [hi] at hb
    exact Rat.le_trans hb hr
  exact (reciprocalInnerPrefix_error (radii n) n).mono hrate

end ComputableAnalysis.RiemannHilbert.RectangularContour
