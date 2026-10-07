import ComputableAnalysis.ModularForms.SquareResidueNormalization

/-! The actual entire Riccati derivative vanishes by its checked square contours. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions PDE.CauchyContour

theorem originalSquareContour_zero_convergence (c : Scalar) (R : QPos) (eps : QPos) :
    ∃ N, ∀ n, N≤n → Small (pairedSquareContourSum c R.val (2^n)) eps.val := by
  obtain ⟨N,hN⟩ := pairedSquareContourLimit_flat_dyadic_convergence c R.val R.property eps
  refine ⟨N,?_⟩
  intro n hn
  have he : (sub (pairedSquareContourLimit c R.val R.property)
      (pairedSquareContourSum c R.val (2^n))).Equiv
      (neg (pairedSquareContourSum c R.val (2^n))) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := sub_valid (pairedSquareContourLimit_valid c R.val R.property)
        (pairedSquareContourSum_valid c R.val (2^n)))
      (hright := neg_valid (pairedSquareContourSum_valid c R.val (2^n)))
    have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := pairedSquareContourLimit_valid c R.val R.property)
      (hright := ofQComplex_valid _) (pairedSquareContourLimit_equiv_zero c R)
    let L := ComplexRawQuotient.ofRaw (pairedSquareContourLimit c R.val R.property)
      (pairedSquareContourLimit_valid c R.val R.property)
    let C := ComplexRawQuotient.ofRaw (pairedSquareContourSum c R.val (2^n))
      (pairedSquareContourSum_valid c R.val (2^n))
    change L=0 at hz
    change L-C= -C
    rw [hz]
    grind only
  have hs := Small.congr
    (sub_valid (pairedSquareContourLimit_valid c R.val R.property) (pairedSquareContourSum_valid c R.val (2^n)))
    (neg_valid (pairedSquareContourSum_valid c R.val (2^n))) he (hN n hn)
  have hnn : (neg (neg (pairedSquareContourSum c R.val (2^n)))).Equiv
      (pairedSquareContourSum c R.val (2^n)) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := neg_valid (neg_valid (pairedSquareContourSum_valid c R.val (2^n))))
      (hright := pairedSquareContourSum_valid c R.val (2^n))
    let Z := ComplexRawQuotient.ofRaw (pairedSquareContourSum c R.val (2^n))
      (pairedSquareContourSum_valid c R.val (2^n))
    change -(-Z)=Z
    grind only
  have hh := SeriesLimitLaws.small_neg hs
  exact Small.congr
    (neg_valid (neg_valid (pairedSquareContourSum_valid c R.val (2^n))))
    (pairedSquareContourSum_valid c R.val (2^n))
    hnn hh

theorem pairedEntire_derivative_normalization_small (c : Scalar) (eps : QPos) :
    Small (mul (pairedEntireRiccatiMap_holomorphic.derivative c trivial).val PDE.CauchyContour.raw) eps.val := by
  let d := pairedEntireRiccatiMap_holomorphic.derivative c trivial
  let eta : QPos := ⟨eps.val/192,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let rho : QPos := ⟨eps.val/(6*1427432192),by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let third : QPos := ⟨eps.val/3,by
    rw [Rat.div_def]; exact Rat.mul_pos eps.property (Rat.inv_pos.mpr (by decide +kernel))⟩
  let R := (pairedEntireRiccatiMap_holomorphic.atPoint c trivial).delta eta
  obtain ⟨N,hN⟩ := originalSquareContour_zero_convergence c R third
  obtain ⟨K,hK⟩ := squareResidueMidpointSum_raw_convergence rho
  let n := N+K
  let S := squareResidueMidpointSum (2^n)
  let C : Scalar := ⟨pairedSquareContourSum c R.val (2^n),pairedSquareContourSum_valid c R.val (2^n)⟩
  have hc : Small C.val third.val := hN n (by dsimp [n]; omega)
  have hs : Small (sub PDE.CauchyContour.raw S.val) rho.val := hK n (by dsimp [n]; omega)
  have hp := Small.mul d.property (sub_valid raw_valid S.property)
    (by decide +kernel : (0:Rat)≤1427432192) (Rat.le_of_lt rho.property)
    (pairedEntireRiccatiMap_global_derivative_bound c) hs
  have ha : Small (sub C.val (mul d.val S.val)) (64*eta.val) :=
    originalSquareContour_derivative_residue_error c R eta (2^n) (Nat.pow_pos (by decide +kernel))
      Rat.le_refl
  have hb := LocalODE.small_add (LocalODE.small_add hp (SeriesLimitLaws.small_neg ha)) hc
  have he : (add (add (mul d.val (sub PDE.CauchyContour.raw S.val))
      (neg (sub C.val (mul d.val S.val)))) C.val).Equiv (mul d.val PDE.CauchyContour.raw) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (add_valid (mul_valid d.property (sub_valid raw_valid S.property))
        (neg_valid (sub_valid C.property (mul_valid d.property S.property)))) C.property)
      (hright := mul_valid d.property raw_valid)
    let D := gridScalarValue d
    let P := ComplexRawQuotient.ofRaw PDE.CauchyContour.raw raw_valid
    let V := gridScalarValue S
    let Q := gridScalarValue C
    change (D*(P-V)+ -(Q-D*V))+Q=D*P
    grind only
  have hsum : (2*1427432192*rho.val+64*eta.val)+third.val=eps.val := by
    dsimp [rho,eta,third]
    simp only [Rat.div_def]
    grind only
  rw [hsum] at hb
  exact Small.congr
    (add_valid (add_valid (mul_valid d.property (sub_valid raw_valid S.property))
      (neg_valid (sub_valid C.property (mul_valid d.property S.property)))) C.property)
    (mul_valid d.property raw_valid) he hb

theorem pairedEntire_derivative_normalization_zero_bound (c : Scalar) :
    Small (mul (pairedEntireRiccatiMap_holomorphic.derivative c trivial).val PDE.CauchyContour.raw) 0 := by
  apply SeriesLimitLaws.small_closed _ 0 (fun n => ((1:Rat)/2)^n)
    (by
      have h := rational_half_geometric_shrinks 1 (by decide +kernel)
      simpa only [Rat.one_mul] using h)
  intro n
  have hp : 0<((1:Rat)/2)^n := Rat.pow_pos (by decide +kernel)
  have hs := pairedEntire_derivative_normalization_small c ⟨((1:Rat)/2)^n,hp⟩
  simpa only [Rat.zero_add] using hs

theorem pairedEntire_derivative_normalization_equiv_zero (c : Scalar) :
    (mul (pairedEntireRiccatiMap_holomorphic.derivative c trivial).val PDE.CauchyContour.raw).Equiv zero := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  have hs := SeriesLimitLaws.small_sub (pairedEntire_derivative_normalization_zero_bound c)
    (Small.zero (by decide +kernel : (0:Rat)≤0))
  simpa only [Rat.zero_add] using hs

theorem pairedEntireRiccatiMap_derivative_equiv_zero (c : Scalar) :
    (pairedEntireRiccatiMap_holomorphic.derivative c trivial).val.Equiv zero := by
  let d := pairedEntireRiccatiMap_holomorphic.derivative c trivial
  let p : Scalar := ⟨PDE.CauchyContour.raw,raw_valid⟩
  have hn : NonzeroBoxSearch.Nonzero p := raw_not_equiv_zero
  let r := RepresentedReciprocal.inverse p hn
  have hi := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid p.property r.property) (hright := ofQComplex_valid _)
    (RepresentedReciprocal.mul_inverse p hn)
  have hz := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid d.property p.property) (hright := ofQComplex_valid _)
    (pairedEntire_derivative_normalization_equiv_zero c)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq (hleft := d.property) (hright := ofQComplex_valid _)
  let D := gridScalarValue d
  let P := gridScalarValue p
  let I := gridScalarValue r
  change P*I=1 at hi
  change D*P=0 at hz
  change D=0
  have hc : D*(P*I)=(D*P)*I := by grind only
  rw [hi,hz] at hc
  grind only

end ComputableAnalysis.ModularForms
