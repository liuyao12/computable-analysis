import ComputableAnalysis.ModularForms.PairedNomeRiccatiDifference

/-! Rational finite-prefix evidence separates the actual lattice Riccati constant from zero. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def pairedZeroSquarePrefix : Nat → Rat
  | 0 => 0
  | n+1 => pairedZeroSquarePrefix n-2*reciprocalSquare (n+1)

theorem pairedZeroSquareTerm_rational (n : Nat) :
    (pairedZeroSquareTerm n).Equiv (ofQComplex ⟨-2*reciprocalSquare (n+1),0⟩) := by
  have he : QComplex.scaleRat 2 ⟨-reciprocalSquare (n+1),0⟩=
      (⟨-2*reciprocalSquare (n+1),0⟩ : QComplex) := by
    simp only [QComplex.scaleRat,QComplex.mk.injEq]
    constructor <;> grind only
  have hs := rationalRectangleScalar_scale ⟨-reciprocalSquare (n+1),0⟩ 2
  rw [he] at hs
  change ofQComplex ⟨-2*reciprocalSquare (n+1),0⟩=scaleRat 2 (ofQComplex ⟨-reciprocalSquare (n+1),0⟩) at hs
  change (scaleRat 2 (ofQComplex ⟨-reciprocalSquare (n+1),0⟩)).Equiv _
  rw [←hs]
  exact equiv_refl _ (ofQComplex_valid _)

theorem pairedZeroSquarePrefix_agreement (N : Nat) :
    (ScalarSeries.block pairedZeroSquareTerm 0 N).Equiv
      (ofQComplex ⟨pairedZeroSquarePrefix N,0⟩) := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    have ha : (ScalarSeries.block pairedZeroSquareTerm 0 (N+1)).Equiv
        (add (ofQComplex ⟨pairedZeroSquarePrefix N,0⟩)
          (ofQComplex ⟨-2*reciprocalSquare (N+1),0⟩)) := by
      simpa only [ScalarSeries.block,Nat.zero_add] using
        add_equiv ih (pairedZeroSquareTerm_rational N)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := ScalarSeries.block_valid pairedZeroSquareTerm (fun _ => scaleRat_valid (ofQComplex_valid _)) 0 (N+1))
      (hright := ofQComplex_valid _)
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := ScalarSeries.block_valid pairedZeroSquareTerm (fun _ => scaleRat_valid (ofQComplex_valid _)) 0 (N+1))
      (hright := add_valid (ofQComplex_valid _) (ofQComplex_valid _)) ha
    rw [hv]
    have he : QComplex.add ⟨pairedZeroSquarePrefix N,0⟩ ⟨-2*reciprocalSquare (N+1),0⟩=
        (⟨pairedZeroSquarePrefix (N+1),0⟩ : QComplex) := by
      simp only [pairedZeroSquarePrefix,QComplex.add,QComplex.mk.injEq]
      constructor <;> grind only
    have hp := rationalPole_add_values ⟨pairedZeroSquarePrefix N,0⟩ ⟨-2*reciprocalSquare (N+1),0⟩
    rw [he] at hp
    exact hp.symm

theorem pairedRiccatiCenterConstant_prefix_error (N : Nat) :
    Small (sub pairedRiccatiCenterConstant.val (ofQComplex ⟨3*pairedZeroSquarePrefix (N+1),0⟩))
      (24*((N+1:Nat):Rat)⁻¹) := by
  let p := ofQComplex ⟨pairedZeroSquarePrefix (N+1),0⟩
  have hs := Small.congr
    (sub_valid pairedZeroSquareSum_valid
      (ScalarSeries.block_valid pairedZeroSquareTerm (fun _ => scaleRat_valid (ofQComplex_valid _)) 0 (N+1)))
    (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))
    (FunctionTheory.sub_congr (equiv_refl _ pairedZeroSquareSum_valid)
      (pairedZeroSquarePrefix_agreement (N+1))) (pairedZeroSquareSum_close N)
  have hb := LocalODE.small_add hs (LocalODE.small_add hs hs)
  have he : (add (sub pairedZeroSquareSum p)
      (add (sub pairedZeroSquareSum p) (sub pairedZeroSquareSum p))).Equiv
      (sub pairedRiccatiCenterConstant.val (ofQComplex ⟨3*pairedZeroSquarePrefix (N+1),0⟩)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))
        (add_valid (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))
          (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))))
      (hright := sub_valid pairedRiccatiCenterConstant.property (ofQComplex_valid _))
    have hq : (⟨3*pairedZeroSquarePrefix (N+1),0⟩ : QComplex)=
        QComplex.add ⟨pairedZeroSquarePrefix (N+1),0⟩
          (QComplex.add ⟨pairedZeroSquarePrefix (N+1),0⟩ ⟨pairedZeroSquarePrefix (N+1),0⟩) := by
      simp only [QComplex.add,QComplex.mk.injEq]
      constructor <;> grind only
    have hv := rationalPole_add_values ⟨pairedZeroSquarePrefix (N+1),0⟩
      (QComplex.add ⟨pairedZeroSquarePrefix (N+1),0⟩ ⟨pairedZeroSquarePrefix (N+1),0⟩)
    rw [←hq,rationalPole_add_values] at hv
    let Z := ComplexRawQuotient.ofRaw pairedZeroSquareSum pairedZeroSquareSum_valid
    let P := ComplexRawQuotient.ofRaw p (ofQComplex_valid _)
    let T := gridScalarValue (rationalRectangleScalar ⟨3*pairedZeroSquarePrefix (N+1),0⟩)
    change T=P+(P+P) at hv
    change (Z-P)+((Z-P)+(Z-P))=(Z+(Z+Z))-T
    rw [hv]
    grind only
  have hr : 8*((N+1:Nat):Rat)⁻¹+(8*((N+1:Nat):Rat)⁻¹+8*((N+1:Nat):Rat)⁻¹)=
      24*((N+1:Nat):Rat)⁻¹ := by grind only
  rw [hr] at hb
  exact Small.congr
    (add_valid (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))
      (add_valid (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))
        (sub_valid pairedZeroSquareSum_valid (ofQComplex_valid _))))
    (sub_valid pairedRiccatiCenterConstant.property (ofQComplex_valid _)) he hb

theorem pairedRiccatiCenterConstant_nonzero : NonzeroBoxSearch.Nonzero pairedRiccatiCenterConstant := by
  intro hz
  have hs := pairedRiccatiCenterConstant_prefix_error 7
  have he : (sub pairedRiccatiCenterConstant.val (ofQComplex ⟨3*pairedZeroSquarePrefix 8,0⟩)).Equiv
      (neg (ofQComplex ⟨3*pairedZeroSquarePrefix 8,0⟩)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid pairedRiccatiCenterConstant.property (ofQComplex_valid _))
      (hright := neg_valid (ofQComplex_valid _))
    have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := pairedRiccatiCenterConstant.property) (hright := ofQComplex_valid _) hz
    let C := gridScalarValue pairedRiccatiCenterConstant
    let P := gridScalarValue (rationalRectangleScalar ⟨3*pairedZeroSquarePrefix 8,0⟩)
    change C=0 at hv
    change C-P= -P
    rw [hv]
    grind only
  have hb := Small.congr (sub_valid pairedRiccatiCenterConstant.property (ofQComplex_valid _))
    (neg_valid (ofQComplex_valid _)) he hs
  have hh := hb.2.1 0 0
  change -(3*pairedZeroSquarePrefix 8)≤24*(8:Rat)⁻¹ at hh
  have hp : 6≤ -(3*pairedZeroSquarePrefix 8) := by decide +kernel
  have ht : 24*(8:Rat)⁻¹<6 := by decide +kernel
  have hc := Rat.le_trans hp hh
  grind only

def pairedRiccatiCenterInverse : Scalar :=
  RepresentedReciprocal.inverse pairedRiccatiCenterConstant pairedRiccatiCenterConstant_nonzero

theorem pairedRiccatiCenterConstant_mul_inverse :
    (mul pairedRiccatiCenterConstant.val pairedRiccatiCenterInverse.val).Equiv (ofQComplex QComplex.one) :=
  RepresentedReciprocal.mul_inverse pairedRiccatiCenterConstant pairedRiccatiCenterConstant_nonzero

end ComputableAnalysis.ModularForms
