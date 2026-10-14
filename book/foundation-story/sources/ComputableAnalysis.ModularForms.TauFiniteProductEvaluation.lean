import ComputableAnalysis.ModularForms.Tau
import ComputableAnalysis.RiemannHilbert.ScalarAlgebra
import ComputableAnalysis.RiemannHilbert.DomainFunctions
import ComputableAnalysis.RiemannHilbert.LocalODESum

/-! Exact finite Euler-product evaluation for the literal tau coefficient recursion.
No infinite-product convergence or discriminant modularity is asserted here. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

/-- Finite represented coefficient evaluation, with explicit validity. -/
def integerCoefficientPrefix (a : Coefficients) (q : Scalar) : Nat → Scalar
  | 0 => ⟨zero,ofQComplex_valid _⟩
  | N+1 =>
    let s := integerCoefficientPrefix a q N
    ⟨add s.val (scaleRat (a N : Rat) (LocalODE.power q.val N)),
      add_valid s.property (scaleRat_valid (LocalODE.power_valid _ q.property N))⟩

private def coefficientSum (a : Coefficients) (Q : ScalarAlgebra.Value) : Nat → ScalarAlgebra.Value
  | 0 => 0
  | N+1 => coefficientSum a Q N + ComplexRawQuotient.scaleRat (a N : Rat) (Q^N)

private theorem prefix_raw (a : Coefficients) (q : Scalar) (N : Nat) :
    ComplexRawQuotient.ofRaw (integerCoefficientPrefix a q N).val
      (integerCoefficientPrefix a q N).property =
      coefficientSum a (ComplexRawQuotient.ofRaw q.val q.property) N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    change ComplexRawQuotient.ofRaw
      (add (integerCoefficientPrefix a q N).val (scaleRat (a N : Rat) (LocalODE.power q.val N))) _ = _
    rw [ComplexRawQuotient.ofRaw_add _ _ (integerCoefficientPrefix a q N).property
      (scaleRat_valid (LocalODE.power_valid _ q.property N)),
      ComplexRawQuotient.ofRaw_scaleRat _ _ (LocalODE.power_valid _ q.property N),
      ScalarAlgebra.ofRaw_power,ih]
    rfl

private theorem scale_sub_int (a b : Int) (Q : ScalarAlgebra.Value) :
    ComplexRawQuotient.scaleRat ((a-b : Int) : Rat) Q =
      ComplexRawQuotient.scaleRat (a:Rat) Q - ComplexRawQuotient.scaleRat (b:Rat) Q := by
  rw [Rat.intCast_sub, Rat.sub_eq_add_neg]
  change ComplexRawQuotient.scaleRat ((a:Rat)+ -(b:Rat)) Q = _
  rw [←ComplexRawQuotient.add_scaleRat,←ComplexRawQuotient.neg_scaleRat]
  rfl

private theorem prefix_subtractShift (m L : Nat) (a : Coefficients) (Q : ScalarAlgebra.Value) :
    coefficientSum (subtractShift m a) Q L = coefficientSum a Q L - Q^m*coefficientSum a Q (L-m) := by
  induction L with
  | zero => simp only [coefficientSum,Nat.zero_sub]; grind only
  | succ L ih =>
    rw [coefficientSum,ih,coefficientSum]
    by_cases hm : m≤L
    · have hs : L+1-m=(L-m)+1 := by omega
      rw [hs,coefficientSum,subtractShift,if_pos hm,scale_sub_int]
      have he : Q^m*ComplexRawQuotient.scaleRat (a (L-m):Rat) (Q^(L-m)) =
          ComplexRawQuotient.scaleRat (a (L-m):Rat) (Q^L) := by
        rw [ComplexRawQuotient.mul_scaleRat]
        have hp : Q^m*Q^(L-m)=Q^L := by
          have hn : m+(L-m)=L := by omega
          grind only
        rw [hp]
      rw [show Q^m*(coefficientSum a Q (L-m)+ComplexRawQuotient.scaleRat (a (L-m):Rat) (Q^(L-m))) =
        Q^m*coefficientSum a Q (L-m)+Q^m*ComplexRawQuotient.scaleRat (a (L-m):Rat) (Q^(L-m)) by grind only,he]
      grind only
    · have hs : L-m=0 := by omega
      have ht : L+1-m=0 := by omega
      rw [subtractShift,if_neg hm,hs,ht,coefficientSum]
      grind only

private theorem prefix_stable (a : Coefficients) (Q : ScalarAlgebra.Value) (N M : Nat)
    (h : ∀ n, N≤n → a n=0) (hn : N≤M) : coefficientSum a Q M=coefficientSum a Q N := by
  induction M with
  | zero =>
    have he : N=0 := by omega
    subst N
    rfl
  | succ M ih =>
    by_cases hm : N≤M
    · rw [coefficientSum,h M hm,show ((0:Int):Rat)=0 by rfl,ComplexRawQuotient.scaleRat_zeroScalar,
        ih hm]
      grind only
    · have he : N=M+1 := by omega
      rw [he]

private theorem subtractShift_support (a : Coefficients) (D m : Nat)
    (h : ∀ n, D<n → a n=0) : ∀ n, D+m<n → subtractShift m a n=0 := by
  intro n hn
  unfold subtractShift
  split
  · rw [h n (by omega),h (n-m) (by omega)]
    rfl
  · exact h n (by omega)

private theorem factorPower_support (a : Coefficients) (D m r : Nat)
    (h : ∀ n, D<n → a n=0) : ∀ n, D+r*m<n → factorPower m r a n=0 := by
  induction r with
  | zero => simpa only [factorPower,Nat.zero_mul,Nat.add_zero] using h
  | succ r ih =>
    have hs := subtractShift_support (factorPower m r a) (D+r*m) m ih
    simpa only [factorPower,Nat.succ_mul,Nat.add_assoc] using hs

private theorem prefix_factor (a : Coefficients) (D m : Nat) (Q : ScalarAlgebra.Value)
    (h : ∀ n, D<n → a n=0) :
    coefficientSum (subtractShift m a) Q (D+m+1) = coefficientSum a Q (D+1)*(1-Q^m) := by
  rw [prefix_subtractShift]
  have hs : D+m+1-m=D+1 := by omega
  rw [hs,prefix_stable a Q (D+1) (D+m+1) (fun n hn => h n (by omega)) (by omega)]
  grind only

private theorem prefix_factorPower (a : Coefficients) (D m r : Nat) (Q : ScalarAlgebra.Value)
    (h : ∀ n, D<n → a n=0) :
    coefficientSum (factorPower m r a) Q (D+r*m+1) = coefficientSum a Q (D+1)*(1-Q^m)^r := by
  induction r with
  | zero => simp only [factorPower,Nat.zero_mul,Nat.add_zero]; grind only
  | succ r ih =>
    have hs := factorPower_support a D m r h
    have hi : D+(r+1)*m+1=(D+r*m)+m+1 := by rw [Nat.add_mul]; simp only [Nat.one_mul,Nat.add_assoc]
    rw [hi,factorPower,prefix_factor _ _ _ _ hs,ih]
    grind only

/-- A finite degree bound, computed without division. -/
def discriminantProductDegree : Nat → Nat
  | 0 => 0
  | N+1 => discriminantProductDegree N + 24*(N+1)

theorem discriminantProduct_support (N n : Nat) (hn : discriminantProductDegree N<n) :
    discriminantProduct N n=0 := by
  induction N generalizing n with
  | zero =>
    change 0<n at hn
    have hn0 : n≠0 := by omega
    simp only [discriminantProduct,unitCoefficients,if_neg hn0]
  | succ N ih =>
    exact factorPower_support (discriminantProduct N) (discriminantProductDegree N) (N+1) 24
      (fun k hk => ih k hk) n hn

/-- Literal finite Euler product, using only represented arithmetic. -/
def finiteDiscriminantEulerProduct (q : Scalar) : Nat → Scalar
  | 0 => ⟨one,ofQComplex_valid _⟩
  | N+1 =>
    let prev := finiteDiscriminantEulerProduct q N
    let factor : Scalar := ⟨sub one (LocalODE.power q.val (N+1)),
      sub_valid (ofQComplex_valid _) (LocalODE.power_valid _ q.property _)⟩
    ⟨mul prev.val (LocalODE.power factor.val 24),
      mul_valid prev.property (LocalODE.power_valid _ factor.property 24)⟩

private theorem quotient_sub (z w : ComplexRaw) (hz : z.Valid) (hw : w.Valid) :
    ComplexRawQuotient.ofRaw (sub z w) (sub_valid hz hw) =
      ComplexRawQuotient.ofRaw z hz - ComplexRawQuotient.ofRaw w hw := by
  change ComplexRawQuotient.ofRaw (add z (neg w)) _ = _
  rw [ComplexRawQuotient.ofRaw_add _ _ hz (neg_valid hw),ComplexRawQuotient.ofRaw_neg _ hw]
  rfl

private theorem finite_product_prefix (q : Scalar) (N : Nat) :
    ComplexRawQuotient.ofRaw (finiteDiscriminantEulerProduct q N).val
      (finiteDiscriminantEulerProduct q N).property =
      coefficientSum (discriminantProduct N) (ComplexRawQuotient.ofRaw q.val q.property)
        (discriminantProductDegree N+1) := by
  induction N with
  | zero =>
    change (1 : ScalarAlgebra.Value)=0+ComplexRawQuotient.scaleRat 1
      ((ComplexRawQuotient.ofRaw q.val q.property)^0)
    rw [ComplexRawQuotient.scaleRat_one]
    grind only
  | succ N ih =>
    have hone : one.Valid := ofQComplex_valid _
    have hpow := LocalODE.power_valid q.val q.property (N+1)
    have hfactor := sub_valid hone hpow
    have hfactor24 := LocalODE.power_valid _ hfactor 24
    have hprev := (finiteDiscriminantEulerProduct q N).property
    change ComplexRawQuotient.ofRaw
      (mul (finiteDiscriminantEulerProduct q N).val
        (LocalODE.power (sub one (LocalODE.power q.val (N+1))) 24))
      (mul_valid hprev hfactor24) = _
    rw [ComplexRawQuotient.ofRaw_mul _ _ hprev hfactor24,
      ScalarAlgebra.ofRaw_power _ hfactor 24,
      quotient_sub one _ hone hpow,ScalarAlgebra.ofRaw_power _ q.property (N+1),ih]
    rw [discriminantProductDegree,discriminantProduct,
      prefix_factorPower _ _ _ _ _ (fun n hn => discriminantProduct_support N n hn)]
    rfl

/-- Exact evaluation of every finite tau product at any represented complex input. -/
theorem discriminantProduct_exact_evaluation (q : Scalar) (N : Nat) :
    (integerCoefficientPrefix (discriminantProduct N) q (discriminantProductDegree N+1)).val.Equiv
      (finiteDiscriminantEulerProduct q N).val := by
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (integerCoefficientPrefix _ q _).property)
    (hright := (finiteDiscriminantEulerProduct q N).property)
  rw [prefix_raw,finite_product_prefix]

theorem integerCoefficientPrefix_congr (a : Coefficients) (q w : Scalar)
    (he : q.val.Equiv w.val) (N : Nat) :
    (integerCoefficientPrefix a q N).val.Equiv (integerCoefficientPrefix a w N).val := by
  induction N with
  | zero => exact equiv_refl _ (ofQComplex_valid _)
  | succ N ih =>
    exact add_equiv ih
      (scaleRat_equiv (LocalODE.power_congr _ _ q.property w.property he N))

theorem finiteDiscriminantEulerProduct_congr (q w : Scalar) (he : q.val.Equiv w.val) (N : Nat) :
    (finiteDiscriminantEulerProduct q N).val.Equiv (finiteDiscriminantEulerProduct w N).val := by
  let L := discriminantProductDegree N+1
  let A := discriminantProduct N
  exact equiv_trans (finiteDiscriminantEulerProduct q N).property
    (integerCoefficientPrefix A q L).property (finiteDiscriminantEulerProduct w N).property
    (equiv_symm (discriminantProduct_exact_evaluation q N))
    (equiv_trans (integerCoefficientPrefix A q L).property
      (integerCoefficientPrefix A w L).property (finiteDiscriminantEulerProduct w N).property
      (integerCoefficientPrefix_congr A q w he L) (discriminantProduct_exact_evaluation w N))

end ComputableAnalysis.ModularForms
