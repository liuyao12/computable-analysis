import ComputableAnalysis.RiemannHilbert.NeumannFinite

/-! Constructing the inverse of a represented linear map close to identity.
All sums and errors are computed from finite iterates and rational bounds. -/
namespace ComputableAnalysis.RiemannHilbert.Neumann
open ComplexRaw FunctionTheory LocalSystem
variable {n : Nat}

def valueMap (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B)) :
    ValueMap (Fiber n) (Fiber n) where
  eval x := VectorGeometric.value (fun k => (power e k).eval x) (initialBound x) q
    (initialBound_nonneg x) hq hsmall (term_bound e q hq he _ (initialBound_nonneg x) x (initialBound_valid x))
  congr {x y} hxy := VectorGeometric.value_congr _ _ (fun k => (power e k).congr hxy)
    (initialBound x) q (initialBound y) q (initialBound_nonneg x) hq (initialBound_nonneg y) hq hsmall hsmall
    (term_bound e q hq he _ (initialBound_nonneg x) x (initialBound_valid x))
    (term_bound e q hq he _ (initialBound_nonneg y) y (initialBound_valid y))

theorem valueMap_agreement (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    (valueMap e q hq hsmall he).eval x ≈
      VectorGeometric.value (fun k => (power e k).eval x) B q hB hq hsmall (term_bound e q hq he B hB x hx) :=
  VectorGeometric.value_congr _ _ (fun _ => Setoid.refl _)
    (initialBound x) q B q (initialBound_nonneg x) hq hB hq hsmall hsmall
    (term_bound e q hq he _ (initialBound_nonneg x) x (initialBound_valid x))
    (term_bound e q hq he B hB x hx)

theorem valueMap_close (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) (N : Nat) :
    CoordinateBound (Fiber.sub ((valueMap e q hq hsmall he).eval x) ((finiteSum e N).eval x)) (4*B*q^N) :=
  bound_congr (Fiber.sub_congr (Setoid.symm (valueMap_agreement e q hq hsmall he B hB x hx)) (Setoid.refl _))
    (VectorGeometric.value_close _ B q hB hq hsmall (term_bound e q hq he B hB x hx) N)

theorem valueMap_bound (e : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q)
    (hsmall : q ≤ (1 : Rat)/2)
    (he : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B → CoordinateBound (e.eval x) (q*B))
    (B : Rat) (hB : 0 ≤ B) (x : Fiber n) (hx : CoordinateBound x B) :
    CoordinateBound ((valueMap e q hq hsmall he).eval x) (4*B) :=
  bound_congr (Setoid.symm (valueMap_agreement e q hq hsmall he B hB x hx))
    (VectorGeometric.value_bound _ B q hB hq hsmall (term_bound e q hq he B hB x hx))

def inverse (f : ValueMap (Fiber n) (Fiber n)) (q : Rat) (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B)) :
    ValueMap (Fiber n) (Fiber n) := valueMap (ValueMap.difference ValueMap.identity f) q hq hsmall hdev

/-- The forward map applied to the constructed Neumann sum is exactly the
supplied input value. Continuity follows from the proved operator estimate. -/
theorem forward_inverse (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f)
    (q : Rat) (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B))
    (x : Fiber n) : f.eval ((inverse f q hq hsmall hdev).eval x) ≈ x := by
  let E := ValueMap.difference ValueMap.identity f
  let B := initialBound x
  let P := 1+q
  let G := inverse f q hq hsmall hdev
  have hB := initialBound_nonneg x
  have hP : 0 ≤ P := by dsimp [P]; grind
  have hC : 0 ≤ (P+1)*B := Rat.mul_nonneg (by grind) hB
  intro i
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun N => 4*((P+1)*B)*q^N)
    (LocalODE.tail_bound_shrinks ((P+1)*B) q hC hq hsmall)
  intro N
  let p := (finiteSum E N).eval x
  have hg := valueMap_close E q hq hsmall hdev B hB x (initialBound_valid x) N
  have hleft := ValueMap.difference_bound f hf P (ValueMap.bound_of_deviation f q hdev)
    (4*B*q^N) (Rat.mul_nonneg (Rat.mul_nonneg (by decide) hB) (Rat.pow_nonneg hq)) (G.eval x) p hg
  have hright := finite_inverse_error f hf q hq hdev B hB x (initialBound_valid x) N
  have hs := bound_add hleft hright
  have hd := bound_congr (Setoid.symm (Fiber.difference_split (f.eval (G.eval x)) x (f.eval p))) hs
  apply (hd i).mono
  rw [Rat.zero_add]
  have hh : 0 ≤ B*q^N := Rat.mul_nonneg hB (Rat.pow_nonneg hq)
  grind

/-- A fully constructed reversible value map: both inverse laws are proved. -/
def valueIso (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f)
    (q : Rat) (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B)) :
    ValueIso (Fiber n) (Fiber n) where
  forward := f
  backward := inverse f q hq hsmall hdev
  forward_backward := forward_inverse f hf q hq hsmall hdev
  backward_forward x := Contraction.reflects f hf q hq hsmall hdev _ x
    (forward_inverse f hf q hq hsmall hdev (f.eval x))

def linearIso (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f)
    (q : Rat) (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B)) : LinearIso n n :=
  ⟨valueIso f hf q hq hsmall hdev, hf⟩

theorem inverse_linear (f : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f)
    (q : Rat) (hq : 0 ≤ q) (hsmall : q ≤ (1 : Rat)/2)
    (hdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B)) :
    IsLinear (inverse f q hq hsmall hdev) :=
  IsLinear.inverse (valueIso f hf q hq hsmall hdev) hf

/-- Different certified contraction constants and equivalent forward programs
give the same inverse value, by the derived inverse implementation law. -/
theorem inverse_congr (f g : ValueMap (Fiber n) (Fiber n)) (hf : IsLinear f) (hg : IsLinear g)
    (hfg : f.Equiv g) (q r : Rat) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hqsmall : q ≤ (1 : Rat)/2) (hrsmall : r ≤ (1 : Rat)/2)
    (hfdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity f).eval x) (q*B))
    (hgdev : ∀ B, 0 ≤ B → ∀ x, CoordinateBound x B →
      CoordinateBound ((ValueMap.difference ValueMap.identity g).eval x) (r*B)) :
    (inverse f q hq hqsmall hfdev).Equiv (inverse g r hr hrsmall hgdev) :=
  ValueIso.inverse_congr (valueIso f hf q hq hqsmall hfdev) (valueIso g hg r hr hrsmall hgdev) hfg

end ComputableAnalysis.RiemannHilbert.Neumann
