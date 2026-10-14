import ComputableAnalysis.ModularForms.PairedRiccatiExtension

/-! Uniform bounds for the constructed unweighted Riccati extension. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem squareBlock_split (k : Nat) :
    reciprocalSquareBlock 0 (k+1)=1+reciprocalSquareBlock 1 k := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    change reciprocalSquareBlock 0 (k+1)+reciprocalSquare (0+(k+1)+1)=
      1+(reciprocalSquareBlock 1 k+reciprocalSquare (1+k+1))
    rw [ih,show 0+(k+1)+1=1+k+1 by omega]
    grind only

private theorem squareBlock_bound (k : Nat) : reciprocalSquareBlock 0 k≤2 := by
  cases k with
  | zero => change (0:Rat)≤2; decide +kernel
  | succ k =>
    rw [squareBlock_split]
    have h := reciprocalSquareBlock_tail 1 k (by omega)
    rw [show ((1:Nat):Rat)⁻¹=1 by decide +kernel] at h
    grind only

theorem pairedRegularDivisionValue_bound (z : Scalar) (hz : Small z.val (1/4)) :
    Small (pairedRegularDivisionValue z hz) 16 := by
  let t := fun n => (pairedRegularDivisionTerm z hz n).val
  have ht : ∀ n, (t n).Valid := fun n => (pairedRegularDivisionTerm z hz n).property
  apply SeriesLimitLaws.small_of_prefix_bound _ (pairedRegularDivisionValue_valid z hz)
    (fun N => ScalarSeries.block t 0 (N+1)) (fun N => ScalarSeries.block_valid t ht 0 (N+1))
    16 (fun N => (8:Rat)*((N+1:Nat):Rat)⁻¹) (pairedReciprocalTail_shrinks 8)
  · exact pairedRegularDivisionValue_close z hz
  · intro N
    apply (inverseSquare_block_bound t 8 (pairedRegularDivisionTerm_bound z hz) 0 (N+1)).mono
    have h := Rat.mul_le_mul_of_nonneg_left (squareBlock_bound (N+1)) (show (0:Rat)≤8 by decide)
    change (8:Rat)*reciprocalSquareBlock 0 (N+1)≤16
    grind only

theorem pairedRiccatiExtension_bound (z : Scalar) (hz : LocalODE.interior (1/4) z) :
    Small (pairedRiccatiExtension z hz).val 2208 := by
  let hq := LocalODE.interior_bound _ z hz
  have ht := pairedRegularDivisionValue_bound z hq
  have hs : Small (pairedRegularPart z hq) 8 := by
    have h := pairedRegularPart_bound z hq (1/4) (by decide +kernel) (by decide +kernel) hq
    simpa only [show (32:Rat)*(1/4)=8 by decide +kernel] using h
  have hss := Small.mul (pairedRegularPart_valid z hq) (pairedRegularPart_valid z hq)
    (show (0:Rat)≤8 by decide) (show (0:Rat)≤8 by decide) hs hs
  have hd := pairedSmallDiskDerivativeValue_bound z hq
  have h := LocalODE.small_add hd (LocalODE.small_add (LocalODE.small_add ht ht) hss)
  rw [show (2048:Rat)+(16+16+2*8*8)=2208 by decide +kernel] at h
  exact h

theorem pairedLaurent_riccati_bound (z : Scalar) (hz : pairedZeroLaurentMap.domain z) :
    Small (add (pairedZeroLaurentMap_holomorphic.derivative z hz).val
      (mul (pairedZeroLaurentMap.eval z hz).val (pairedZeroLaurentMap.eval z hz).val)) 2208 :=
  Small.congr (pairedRiccatiExtension z hz.1).property
    (add_valid (pairedZeroLaurentMap_holomorphic.derivative z hz).property
      (mul_valid (pairedZeroLaurentMap.eval z hz).property (pairedZeroLaurentMap.eval z hz).property))
    (equiv_symm (pairedLaurent_riccati_extension z hz)) (pairedRiccatiExtension_bound z hz.1)

end ComputableAnalysis.ModularForms
