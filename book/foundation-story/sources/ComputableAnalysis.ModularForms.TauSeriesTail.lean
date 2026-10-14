import ComputableAnalysis.ModularForms.TauComplexTermBounds

/-! Geometric tails for actual represented integer coefficient prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert

private theorem half_power_add (K M : Nat) :
    (1/2:Rat)^(K+M)=(1/2:Rat)^K*(1/2:Rat)^M := by
  induction M with
  | zero => simp only [Nat.add_zero,Rat.pow_zero,Rat.mul_one]
  | succ M ih =>
    change (1/2:Rat)^((K+M)+1)=(1/2:Rat)^K*(1/2:Rat)^(M+1)
    rw [Rat.pow_succ,ih,Rat.pow_succ]
    grind only

/-- A supplied geometric monomial bound gives an actual represented prefix tail. -/
theorem integerCoefficientPrefix_geometric_tail (a : Coefficients) (q : Scalar)
    (hterm : ∀ n, Small (scaleRat (a n:Rat) (LocalODE.power q.val n)) (2*(1/2:Rat)^n))
    (K M : Nat) :
    Small (sub (integerCoefficientPrefix a q (K+M)).val (integerCoefficientPrefix a q K).val)
      (4*(1/2:Rat)^K) := by
  have haux : ∀ M, Small
      (sub (integerCoefficientPrefix a q (K+M)).val (integerCoefficientPrefix a q K).val)
      (4*(1/2:Rat)^K*(1-(1/2:Rat)^M)) := by
    intro M
    induction M with
    | zero =>
      have he := add_neg_equiv (integerCoefficientPrefix a q K).val (integerCoefficientPrefix a q K).property
      have hzero : Small zero (4*(1/2:Rat)^K*(1-(1/2:Rat)^0)) := by
        apply Small.zero
        rw [Rat.pow_zero]
        grind only
      exact Small.congr (ofQComplex_valid _) (sub_valid (integerCoefficientPrefix a q K).property
        (integerCoefficientPrefix a q K).property) (equiv_symm he) hzero
    | succ M ih =>
      let P := integerCoefficientPrefix a q (K+M)
      let Q := integerCoefficientPrefix a q K
      let T : Scalar := ⟨scaleRat (a (K+M):Rat) (LocalODE.power q.val (K+M)),
        scaleRat_valid (LocalODE.power_valid _ q.property _)⟩
      have he : (add (sub P.val Q.val) T.val).Equiv
          (sub (integerCoefficientPrefix a q (K+(M+1))).val Q.val) := by
        apply ComplexRawQuotient.equiv_of_ofRaw_eq
          (hleft := add_valid (sub_valid P.property Q.property) T.property)
          (hright := sub_valid (integerCoefficientPrefix a q (K+(M+1))).property Q.property)
        let p := ComplexRawQuotient.ofRaw P.val P.property
        let b := ComplexRawQuotient.ofRaw Q.val Q.property
        let t := ComplexRawQuotient.ofRaw T.val T.property
        change (p-b)+t=(p+t)-b
        grind only
      have h := Small.congr (add_valid (sub_valid P.property Q.property) T.property)
        (sub_valid (integerCoefficientPrefix a q (K+(M+1))).property Q.property) he
        (LocalODE.small_add ih (hterm (K+M)))
      have hb : 4*(1/2:Rat)^K*(1-(1/2:Rat)^M)+2*(1/2:Rat)^(K+M)=
          4*(1/2:Rat)^K*(1-(1/2:Rat)^(M+1)) := by
        rw [half_power_add,Rat.pow_succ]
        grind only
      rw [hb] at h
      exact h
  have hp : 0≤(1/2:Rat)^M := Rat.pow_nonneg (by decide +kernel)
  have hm := Rat.mul_le_mul_of_nonneg_left (show 1-(1/2:Rat)^M≤1 by grind only)
    (Rat.mul_nonneg (show (0:Rat)≤4 by decide +kernel)
      (Rat.pow_nonneg (show (0:Rat)≤1/2 by decide +kernel) : 0≤(1/2:Rat)^K))
  exact (haux M).mono (by simpa only [Rat.mul_one] using hm)

/-- Every finite Euler polynomial has the same represented geometric tail bound. -/
theorem discriminantProduct_complex_tail (q : Scalar) (hq : Small q.val (1/1024)) (N K M : Nat) :
    Small (sub (integerCoefficientPrefix (discriminantProduct N) q (K+M)).val
      (integerCoefficientPrefix (discriminantProduct N) q K).val) (4*(1/2:Rat)^K) :=
  integerCoefficientPrefix_geometric_tail _ q (discriminantProduct_complex_term_bound q hq N) K M

/-- Ordinary prefixes of the unnormalized tau series satisfy a geometric Cauchy bound. -/
theorem tauSeries_complex_tail (q : Scalar) (hq : Small q.val (1/1024)) (K M : Nat) :
    Small (sub (integerCoefficientPrefix (fun n => tau (n+1)) q (K+M)).val
      (integerCoefficientPrefix (fun n => tau (n+1)) q K).val) (4*(1/2:Rat)^K) :=
  integerCoefficientPrefix_geometric_tail _ q (tau_complex_term_bound q hq) K M

end ComputableAnalysis.ModularForms
