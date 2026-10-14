import ComputableAnalysis.ModularForms.UpperPositiveLatticeRows

/-! Negation symmetry of actual even-power lattice terms and finite rows. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory

private theorem orderNeg_involution (u : QuadraticOrder163) :
    QuadraticOrder163.neg (QuadraticOrder163.neg u)=u := by
  apply QuadraticOrder163.ext <;> simp only [QuadraticOrder163.neg,Int.neg_neg]

private theorem orderNeg_nonzero (u : QuadraticOrder163)
    (hu : u≠QuadraticOrder163.zero) : QuadraticOrder163.neg u≠QuadraticOrder163.zero := by
  intro he
  have h := congrArg QuadraticOrder163.neg he
  rw [orderNeg_involution] at h
  exact hu h

private theorem evenPower_neg (x : ScalarAlgebra.Value) (k : Nat) :
    (-x)^(2*k)=x^(2*k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hi : 2*(k+1)=2*k+2 := by omega
    rw [hi,Lean.Grind.Semiring.pow_add,Lean.Grind.Semiring.pow_add,ih]
    have htwo : (-x)^2=x^2 := by grind only
    rw [htwo]

theorem latticeVector_neg (z : Scalar) (u : QuadraticOrder163) :
    (latticeVector z (QuadraticOrder163.neg u)).val.Equiv
      (ComplexRaw.neg (latticeVector z u).val) := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (latticeVector z (QuadraticOrder163.neg u)).property)
    (hright := neg_valid (latticeVector z u).property)
  change ComplexRawQuotient.ofRaw (integerAffine (-u.y) (-u.x) z.val) _=
    -ComplexRawQuotient.ofRaw (integerAffine u.y u.x z.val) (integerAffine_valid _ _ z.property)
  rw [integerAffine_class,integerAffine_class]
  grind only

theorem latticeInverse_neg (z : Scalar) (hz : InUpperHalfPlane z.val)
    (u : QuadraticOrder163) (hu : u≠QuadraticOrder163.zero) :
    (latticeInverse z hz (QuadraticOrder163.neg u) (orderNeg_nonzero u hu)).val.Equiv
      (ComplexRaw.neg (latticeInverse z hz u hu).val) := by
  apply RepresentedReciprocal.inverse_unique
    (latticeVector z (QuadraticOrder163.neg u))
    (latticeVector_nonzero z hz _ (orderNeg_nonzero u hu))
    ⟨ComplexRaw.neg (latticeInverse z hz u hu).val,neg_valid (latticeInverse z hz u hu).property⟩
  have hv := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := (latticeVector z (QuadraticOrder163.neg u)).property)
    (hright := neg_valid (latticeVector z u).property) (latticeVector_neg z u)
  have hI := ComplexRawQuotient.ofRaw_eq_ofRaw
    (hleft := mul_valid (latticeVector z u).property (latticeInverse z hz u hu).property)
    (hright := ofQComplex_valid _) (latticeInverse_product z hz u hu)
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := mul_valid (latticeVector z (QuadraticOrder163.neg u)).property
      (neg_valid (latticeInverse z hz u hu).property))
    (hright := ofQComplex_valid _)
  let V := ComplexRawQuotient.ofRaw (latticeVector z u).val (latticeVector z u).property
  let W := ComplexRawQuotient.ofRaw (latticeVector z (QuadraticOrder163.neg u)).val
    (latticeVector z (QuadraticOrder163.neg u)).property
  let I := ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val (latticeInverse z hz u hu).property
  change W= -V at hv
  change V*I=1 at hI
  change W*(-I)=1
  generalize V=v,W=w,I=i at hv hI ⊢
  grind only

/-- Even reciprocal powers are unchanged by actual lattice-point negation. -/
theorem upperPointPower_even_neg (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k : Nat) (u : QuadraticOrder163) :
    (upperPointPower z hz (2*k) (QuadraticOrder163.neg u)).Equiv
      (upperPointPower z hz (2*k) u) := by
  by_cases hu : u≠QuadraticOrder163.zero
  · simp only [upperPointPower,dif_pos hu,dif_pos (orderNeg_nonzero u hu)]
    have hI := ComplexRawQuotient.ofRaw_eq_ofRaw
      (hleft := (latticeInverse z hz (QuadraticOrder163.neg u) (orderNeg_nonzero u hu)).property)
      (hright := neg_valid (latticeInverse z hz u hu).property) (latticeInverse_neg z hz u hu)
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := LocalODE.power_valid _ (latticeInverse z hz _ (orderNeg_nonzero u hu)).property (2*k))
      (hright := LocalODE.power_valid _ (latticeInverse z hz u hu).property (2*k))
    rw [ScalarAlgebra.ofRaw_power _ (latticeInverse z hz (QuadraticOrder163.neg u) (orderNeg_nonzero u hu)).property,
      ScalarAlgebra.ofRaw_power _ (latticeInverse z hz u hu).property]
    change ComplexRawQuotient.ofRaw
      (latticeInverse z hz (QuadraticOrder163.neg u) (orderNeg_nonzero u hu)).val
        (latticeInverse z hz (QuadraticOrder163.neg u) (orderNeg_nonzero u hu)).property=
      -ComplexRawQuotient.ofRaw (latticeInverse z hz u hu).val
        (latticeInverse z hz u hu).property at hI
    rw [hI]
    exact evenPower_neg _ k
  · have he : u=QuadraticOrder163.zero := by exact Classical.byContradiction hu
    subst u
    have hn : QuadraticOrder163.neg QuadraticOrder163.zero=QuadraticOrder163.zero := by decide
    rw [hn]
    exact equiv_refl _ (upperPointPower_valid z hz (2*k) _)

open QuadraticOrder163 in
private theorem rowPoints_neg_perm (N : Nat) (y : Int) :
    ((latticeRowPoints N y).map QuadraticOrder163.neg).Perm (latticeRowPoints N (-y)) := by
  have hnodup : ((latticeRowPoints N y).map QuadraticOrder163.neg).Nodup := by
    apply List.Pairwise.map _ _ (latticeRowPoints_nodup N y)
    intro u v hne he
    have h := congrArg QuadraticOrder163.neg he
    rw [orderNeg_involution,orderNeg_involution] at h
    exact hne h
  apply (List.perm_ext_iff_of_nodup hnodup (latticeRowPoints_nodup N (-y))).mpr
  intro u
  constructor
  · intro hu
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hu
    have hb := (mem_latticeRowPoints v N y).mp hv
    apply (mem_latticeRowPoints (QuadraticOrder163.neg v) N (-y)).mpr
    refine ⟨orderNeg_nonzero v hb.1,?_,?_,?_⟩
    · change -v.y= -y
      rw [hb.2.1]
    · change -(N:Int)≤ -v.x
      omega
    · change -v.x≤(N:Int)
      omega
  · intro hu
    have hb := (mem_latticeRowPoints u N (-y)).mp hu
    apply List.mem_map.mpr
    refine ⟨QuadraticOrder163.neg u,?_,orderNeg_involution u⟩
    apply (mem_latticeRowPoints (QuadraticOrder163.neg u) N y).mpr
    refine ⟨orderNeg_nonzero u hb.1,?_,?_,?_⟩
    · change -u.y=y
      omega
    · change -(N:Int)≤ -u.x
      omega
    · change -u.x≤(N:Int)
      omega

/-- Negative and positive finite rows have identical actual values in even weight. -/
theorem upperLatticeFiniteRow_even_neg (z : Scalar) (hz : InUpperHalfPlane z.val)
    (k N : Nat) (y : Int) :
    (upperLatticeFiniteRow z hz (2*k) N (-y)).val.Equiv
      (upperLatticeFiniteRow z hz (2*k) N y).val := by
  have hreindex := representedSum_reindex (upperPointPower z hz (2*k))
    (upperPointPower_valid z hz (2*k)) (rowPoints_neg_perm N y)
  have hterms := representedSum_map_equiv (QuadraticOrder163.latticeRowPoints N y)
    (fun u => upperPointPower z hz (2*k) (QuadraticOrder163.neg u))
    (upperPointPower z hz (2*k)) (upperPointPower_even_neg z hz k)
  have hv : (LocalODE.sum (((QuadraticOrder163.latticeRowPoints N y).map QuadraticOrder163.neg).map
      (upperPointPower z hz (2*k)))).Valid := by
    apply LocalODE.sum_valid
    intro zz hzz
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hzz
    exact upperPointPower_valid z hz (2*k) u
  exact equiv_trans (upperLatticeFiniteRow z hz (2*k) N (-y)).property hv
    (upperLatticeFiniteRow z hz (2*k) N y).property (equiv_symm hreindex) (by
      rw [List.map_map]
      change (LocalODE.sum ((QuadraticOrder163.latticeRowPoints N y).map
        (fun u => upperPointPower z hz (2*k) (QuadraticOrder163.neg u)))).Equiv
        (LocalODE.sum ((QuadraticOrder163.latticeRowPoints N y).map (upperPointPower z hz (2*k))))
      exact hterms)

end ComputableAnalysis.ModularForms
