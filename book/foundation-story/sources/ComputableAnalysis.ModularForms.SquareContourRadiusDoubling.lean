import ComputableAnalysis.ModularForms.OuterSquareContourAssembly
import ComputableAnalysis.ModularForms.PairedSquareFlatSumAgreement
import ComputableAnalysis.ModularForms.ExecutableSquareContour

/-! Proved equality of the actual contour candidates at doubled radii. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

theorem represented_sub_telescope (a b c : Scalar) :
    (add (sub a.val b.val) (sub b.val c.val)).Equiv (sub a.val c.val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := add_valid (sub_valid a.property b.property) (sub_valid b.property c.property))
    (hright := sub_valid a.property c.property)
  let A := gridScalarValue a
  let B := gridScalarValue b
  let C := gridScalarValue c
  change (A-B)+(B-C)=A-C
  grind only

theorem pairedSquareContourLimit_doubled_radius (c : Scalar) (R : QPos) :
    (pairedSquareContourLimit c (2*R.val) (Rat.mul_pos (by decide +kernel) R.property)).Equiv
      (pairedSquareContourLimit c R.val R.property) := by
  let h2 : 0<2*R.val := Rat.mul_pos (by decide +kernel) R.property
  let X : Scalar := ⟨pairedSquareContourLimit c (2*R.val) h2,pairedSquareContourLimit_valid c (2*R.val) h2⟩
  let Y : Scalar := ⟨pairedSquareContourLimit c R.val R.property,pairedSquareContourLimit_valid c R.val R.property⟩
  let p := fun n => (⟨pairedSquareContourSum c R.val (2^n),pairedSquareContourSum_valid c R.val (2^n)⟩ : Scalar)
  apply representedSequenceLimit_unique p X Y
  · intro eps
    let eta : QPos := ⟨eps.val/2,by
      rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
    obtain ⟨A,hA⟩ := pairedSquareContourLimit_flat_dyadic_convergence c (2*R.val) h2 eta
    obtain ⟨B,hB⟩ := pairedSquareContourSum_doubled_radius_difference_converges_zero c R eta
    refine ⟨A+B, ?_⟩
    intro n hn
    let q : Scalar := ⟨pairedSquareContourSum c (2*R.val) (2*(2^n)),
      pairedSquareContourSum_valid c (2*R.val) (2*(2^n))⟩
    have hpow : 2^(n+1)=2*(2^n) := by rw [Nat.pow_succ]; omega
    have ha := hA (n+1) (by omega)
    rw [hpow] at ha
    have hb := LocalODE.small_add ha (hB n (by omega))
    have hc := Small.congr
      (add_valid (sub_valid X.property q.property) (sub_valid q.property (p n).property))
      (sub_valid X.property (p n).property) (represented_sub_telescope X q (p n)) hb
    have he : eta.val+eta.val=eps.val := by change eps.val/2+eps.val/2=eps.val; grind only
    rw [he] at hc
    exact hc
  · exact pairedSquareContourLimit_flat_dyadic_convergence c R.val R.property

theorem executableSquareContour_doubled_radius (c : Scalar) (R : QPos) :
    (executableSquareContour c (2*R.val)).Equiv (executableSquareContour c R.val) := by
  have h2 : 0<2*R.val := Rat.mul_pos (by decide +kernel) R.property
  exact equiv_trans (executableSquareContour_valid c (2*R.val) h2)
    (pairedSquareContourLimit_valid c (2*R.val) h2) (executableSquareContour_valid c R.val R.property)
    (executableSquareContour_agreement c (2*R.val) h2)
    (equiv_trans (pairedSquareContourLimit_valid c (2*R.val) h2)
      (pairedSquareContourLimit_valid c R.val R.property) (executableSquareContour_valid c R.val R.property)
      (pairedSquareContourLimit_doubled_radius c R)
      (equiv_symm (executableSquareContour_agreement c R.val R.property)))

def doubledContourRadius (R : QPos) : Nat → QPos
  | 0 => R
  | n+1 => ⟨2*(doubledContourRadius R n).val,
      Rat.mul_pos (by decide +kernel) (doubledContourRadius R n).property⟩

theorem doubledContourRadius_value (R : QPos) (n : Nat) :
    (doubledContourRadius R n).val=R.val*(2:Rat)^n := by
  induction n with
  | zero => simp only [doubledContourRadius,Rat.pow_zero,Rat.mul_one]
  | succ n ih =>
    change 2*(doubledContourRadius R n).val=R.val*2^(n+1)
    rw [ih,Rat.pow_succ]
    grind only

theorem executableSquareContour_iterated_doubling (c : Scalar) (R : QPos) (n : Nat) :
    (executableSquareContour c (doubledContourRadius R n).val).Equiv
      (executableSquareContour c R.val) := by
  induction n with
  | zero => exact equiv_refl _ (executableSquareContour_valid c R.val R.property)
  | succ n ih =>
    exact equiv_trans
      (executableSquareContour_valid c (doubledContourRadius R (n+1)).val (doubledContourRadius R (n+1)).property)
      (executableSquareContour_valid c (doubledContourRadius R n).val (doubledContourRadius R n).property)
      (executableSquareContour_valid c R.val R.property)
      (executableSquareContour_doubled_radius c (doubledContourRadius R n)) ih

end ComputableAnalysis.ModularForms

