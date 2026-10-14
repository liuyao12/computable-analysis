import ComputableAnalysis.RiemannHilbert.LocalSystemUniform

/-! Differences of linear maps and quantitative reflection near the identity. -/
namespace ComputableAnalysis.RiemannHilbert
open ComplexRaw FunctionTheory LocalSystem

namespace Fiber
theorem sub_zero (x : Fiber n) : sub x (Fiber.zero n) ≈ x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (sub x (Fiber.zero n)).property i) (hright := x.property i)
  change ComplexRawQuotient.ofRaw (x.val i) (x.property i)-0 = ComplexRawQuotient.ofRaw (x.val i) (x.property i)
  grind

theorem bound_zero_equiv {x : Fiber n} (hx : CoordinateBound x 0) : x ≈ Fiber.zero n := by
  intro i
  exact SeriesLimitLaws.equiv_of_small_sub_zero _ ComplexRaw.zero (by
    have hs := SeriesLimitLaws.small_sub (hx i) (Small.zero (by decide : (0 : Rat) ≤ 0))
    simpa only [Rat.add_zero] using hs)

theorem sub_add_sub (x y u v : Fiber n) :
    sub (add x u) (add y v) ≈ add (sub x y) (sub u v) :=
  fun i => SeriesLimitLaws.addition_difference _ _ _ _ (x.property i) (y.property i) (u.property i) (v.property i)
end Fiber

namespace ValueMap
variable {n m : Nat}

def difference (f g : ValueMap (Fiber n) (Fiber m)) : ValueMap (Fiber n) (Fiber m) :=
  ⟨fun x => Fiber.sub (f.eval x) (g.eval x), fun h => Fiber.sub_congr (f.congr h) (g.congr h)⟩

theorem difference_linear (f g : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) (hg : IsLinear g) :
    IsLinear (difference f g) := by
  constructor
  · intro x y
    exact Setoid.trans (Fiber.sub_congr (hf.1 x y) (hg.1 x y)) (Fiber.sub_add_sub _ _ _ _)
  · intro c x
    exact Setoid.trans (Fiber.sub_congr (hf.2 c x) (hg.2 c x)) (Setoid.symm (Fiber.scale_sub c _ _))

theorem complement (f : ValueMap (Fiber n) (Fiber n)) (x : Fiber n) :
    Fiber.sub x ((difference identity f).eval x) ≈ f.eval x := by
  intro i
  apply ComplexRawQuotient.equiv_of_ofRaw_eq
    (hleft := (Fiber.sub x ((difference identity f).eval x)).property i) (hright := (f.eval x).property i)
  change ComplexRawQuotient.ofRaw (x.val i) (x.property i)-
    (ComplexRawQuotient.ofRaw (x.val i) (x.property i)-
      ComplexRawQuotient.ofRaw ((f.eval x).val i) ((f.eval x).property i)) =
      ComplexRawQuotient.ofRaw ((f.eval x).val i) ((f.eval x).property i)
  grind

theorem bound_of_deviation (f : ValueMap (Fiber n) (Fiber n)) (q : Rat)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((difference identity f).eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound (f.eval x) ((1+q)*B) := by
  have hs := bound_congr (complement f x) (bound_sub hx (hdev B hB x hx))
  have he : B+q*B=(1+q)*B := by grind
  rw [he] at hs; exact hs

theorem difference_bound (f : ValueMap (Fiber n) (Fiber m)) (hf : IsLinear f) (P : Rat)
    (hbound : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (f.eval x) (P*B))
    (B : Rat) (hB : 0 ≤ B) (x y : Fiber n) (hxy : CoordinateBound (Fiber.sub x y) B) :
    CoordinateBound (Fiber.sub (f.eval x) (f.eval y)) (P*B) :=
  bound_congr (hf.sub x y) (hbound B hB (Fiber.sub x y) hxy)

end ValueMap

namespace Contraction
variable {n : Nat}

/-- A fixed point of a small homogeneous contraction is zero; iteration of
justified bounds proves this without a norm value or a fixed-point axiom. -/
theorem fixedpoint_zero (e : ValueMap (Fiber n) (Fiber n)) (q : Rat)
    (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (x : Fiber n) (hfix : e.eval x ≈ x) : x ≈ Fiber.zero n := by
  let B := initialBound x
  have hB := initialBound_nonneg x
  have hb : ∀ k : Nat, CoordinateBound x (B*q^k) := by
    intro k
    induction k with
    | zero => simpa only [Rat.pow_zero, Rat.mul_one] using initialBound_valid x
    | succ k ih =>
      have hs := bound_congr hfix (he (B*q^k) (Rat.mul_nonneg hB (Rat.pow_nonneg hq)) x ih)
      have hh : q*(B*q^k)=B*q^(k+1) := by rw [Rat.pow_succ]; grind
      rw [hh] at hs; exact hs
  apply Fiber.bound_zero_equiv
  intro i
  apply SeriesLimitLaws.small_closed _ 0 (fun k => 4*B*q^k) (LocalODE.tail_bound_shrinks B q hB hq hsmall)
  intro k
  apply (hb k i).mono
  rw [Rat.zero_add]
  have hh : 0 ≤ B*q^k := Rat.mul_nonneg hB (Rat.pow_nonneg hq)
  grind

/-- A linear map whose deviation from identity is a small contraction reflects
value equality. Injectivity is derived, not included among the inputs. -/
theorem reflects (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f) (q : Rat)
    (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B))
    (x y : Fiber n) (hxy : f.eval x ≈ f.eval y) : x ≈ y := by
  let d := Fiber.sub x y
  have hfd : f.eval d ≈ Fiber.zero n := Setoid.trans (hf.sub x y)
    (Fiber.bound_zero_equiv (Fiber.sub_zero_bound hxy))
  have hfix : (ValueMap.difference ValueMap.identity f).eval d ≈ d :=
    Setoid.trans (Fiber.sub_congr (Setoid.refl d) hfd) (Fiber.sub_zero d)
  have hd := fixedpoint_zero _ q hq hsmall hdev d hfix
  exact fun i => SeriesLimitLaws.equiv_of_small_sub_zero _ _
    (Small.congr (ofQComplex_valid _) (d.property i) (equiv_symm (hd i)) (Small.zero (by decide)))

end Contraction
end ComputableAnalysis.RiemannHilbert
