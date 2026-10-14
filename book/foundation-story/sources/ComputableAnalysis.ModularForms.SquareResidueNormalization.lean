import ComputableAnalysis.ModularForms.FiniteSquareAffineResidue
import ComputableAnalysis.ModularForms.ExponentialLegacyTail

/-! Midpoint residue samples and the independently certified pole normalization. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

def uniformPoleCells (M k K : Nat) : List TaggedCell :=
  (List.range' k K).map (fun (v : Nat) =>
    ⟨(v:Rat)/(M:Rat),((v+1:Nat):Rat)/(M:Rat),squareMidpointParameter M v⟩)

theorem uniformPoleCell_weight (M v : Nat) (hM : 0<M) :
    ((v+1:Nat):Rat)/(M:Rat)-(v:Rat)/(M:Rat)=(M:Rat)⁻¹ := by
  rw [Rat.natCast_add]
  change ((v:Rat)+1)/(M:Rat)-(v:Rat)/(M:Rat)=(M:Rat)⁻¹
  simp only [Rat.div_def]
  grind only

theorem uniformPoleCells_value (M k K : Nat) (hM : 0<M) :
    gridScalarValue (rationalRectangleScalar (taggedSum (uniformPoleCells M k K)))=
      ComplexRawQuotient.scaleRat ((M:Rat)⁻¹)
        (gridValueSum K (fun v => gridScalarValue
          (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel (squareMidpointParameter M (k+v))⟩))) := by
  induction K generalizing k with
  | zero =>
    simp only [uniformPoleCells,List.range'_zero,List.map_nil,taggedSum,gridValueSum]
    change (0:ScalarAlgebra.Value)=ComplexRawQuotient.scaleRat ((M:Rat)⁻¹) 0
    exact (ComplexRawQuotient.scaleRat_zero _).symm
  | succ K ih =>
    simp only [uniformPoleCells,List.range'_succ,List.map_cons,taggedSum]
    rw [rationalPole_add_values,rationalPole_scale_values,uniformPoleCell_weight M k hM,density_exact]
    change ComplexRawQuotient.scaleRat ((M:Rat)⁻¹)
      (gridScalarValue (rationalRectangleScalar ⟨0,8*ArctanGeometry.integralKernel (squareMidpointParameter M k)⟩))+
      gridScalarValue (rationalRectangleScalar (taggedSum (uniformPoleCells M (k+1) K)))=_
    rw [ih (k+1),gridValueSum_head_shift,ComplexRawQuotient.scaleRat_add]
    simp only [Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem stageCells_uniform (n : Nat) :
    stageCells n=uniformPoleCells (2^n) 0 (2^n) := by
  unfold stageCells
  rw [ArctanGeometry.arctanAreaLoopState_one_intervals_eq_uniform]
  simp only [midpointCells,List.map_map,uniformPoleCells,←List.range_eq_range']
  congr 1
  funext v
  dsimp only [Function.comp_def]
  congr 1
  simp only [squareMidpointParameter,Nat.succ_eq_add_one,Rat.natCast_add]
  change ((v:Rat)/(2^n:Nat)+(↑v+1)/(2^n:Nat))/2=((v:Rat)+1/2)/(2^n:Nat)
  simp only [Rat.div_def]
  grind only

theorem squareResidueMidpointSum_stage_agreement (n : Nat) :
    (squareResidueMidpointSum (2^n)).val.Equiv
      (ofQComplex (taggedSum (stageCells n))) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (squareResidueMidpointSum (2^n)).property)
    (hright := ofQComplex_valid _)
  rw [stageCells_uniform]
  have h := uniformPoleCells_value (2^n) 0 (2^n) (Nat.pow_pos (by decide +kernel))
  change _=gridScalarValue (rationalRectangleScalar (taggedSum (uniformPoleCells (2^n) 0 (2^n))))
  rw [h]
  change ComplexRawQuotient.scaleRat ((2^n:Nat):Rat)⁻¹
    (gridScalarValue (gridScalarSum (2^n) (fun v => rationalRectangleScalar
      ⟨0,8*ArctanGeometry.integralKernel (squareMidpointParameter (2^n) v)⟩)))=_
  rw [gridScalarSum_value]
  simp only [Nat.zero_add]

theorem squareResidueMidpointSum_raw_error (n : Nat) :
    Small (sub PDE.CauchyContour.raw (squareResidueMidpointSum (2^n)).val)
      (16/((2^n:Nat):Rat)) := by
  have hp := raw_encloses_stageSum n
  have hn : 0<16/((2^n:Nat):Rat) :=
    by
      rw [Rat.div_def]
      exact Rat.mul_pos (by decide +kernel)
        (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (Nat.pow_pos (by decide +kernel))))
  have hb := point_in_box_error PDE.CauchyContour.raw raw_valid (taggedSum (stageCells n)) n
    (16/((2^n:Nat):Rat)) hp
    (by rw [raw_width_zero]; exact Rat.le_of_lt hn) (raw_height_geometric n)
  exact Small.congr (sub_valid raw_valid (ofQComplex_valid _))
    (sub_valid raw_valid (squareResidueMidpointSum (2^n)).property)
    (FunctionTheory.sub_congr (equiv_refl _ raw_valid)
      (equiv_symm (squareResidueMidpointSum_stage_agreement n))) hb

theorem squareResidueMidpointSum_raw_convergence (eps : QPos) :
    ∃ N, ∀ n, N≤n →
      Small (sub PDE.CauchyContour.raw (squareResidueMidpointSum (2^n)).val) eps.val := by
  obtain ⟨N,hN⟩ := rational_half_geometric_shrinks 16 (by decide +kernel) eps
  refine ⟨N,?_⟩
  intro n hn
  have he : 16/((2^n:Nat):Rat)=16*((1:Rat)/2)^n := by
    have hi : ((2^n:Nat):Rat)⁻¹=((1:Rat)/2)^n := by
      clear hn
      induction n with
      | zero => decide +kernel
      | succ n ih =>
        rw [Nat.pow_succ,Rat.natCast_mul,Rat.inv_mul_rev,Rat.pow_succ,ih]
        change (2:Rat)⁻¹*((1:Rat)/2)^n=((1:Rat)/2)^n*(1/2)
        simp only [Rat.div_def,Rat.one_mul]
        grind only
    simp only [Rat.div_def,hi]
  have hb := hN n hn
  change 16*((1:Rat)/2)^n≤eps.val at hb
  rw [←he] at hb
  exact (squareResidueMidpointSum_raw_error n).mono hb

theorem squareResidueMidpointSum_twoPiI_convergence (eps : QPos) :
    ∃ N, ∀ n, N≤n →
      Small (sub twoPiI (squareResidueMidpointSum (2^n)).val) eps.val := by
  obtain ⟨N,hN⟩ := squareResidueMidpointSum_raw_convergence eps
  refine ⟨N,?_⟩
  intro n hn
  exact Small.congr (sub_valid raw_valid (squareResidueMidpointSum (2^n)).property)
    (sub_valid twoPiI_valid (squareResidueMidpointSum (2^n)).property)
    (FunctionTheory.sub_congr raw_equiv_twoPiI
      (equiv_refl _ (squareResidueMidpointSum (2^n)).property)) (hN n hn)

end ComputableAnalysis.ModularForms
