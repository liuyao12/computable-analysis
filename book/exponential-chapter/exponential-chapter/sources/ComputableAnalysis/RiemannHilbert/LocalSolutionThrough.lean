import ComputableAnalysis.RiemannHilbert.LocalSystemInverse

/-! Actual holomorphic horizontal solutions normalized at any represented
point of the local chart, with derived uniqueness from uniform errors. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

def throughValue (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) : Fiber n :=
  localValue a (initialFromValue a ha M K hM hK hMK haB p hp v) M K hM hK hMK haB z hz

def throughCoordinate (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n) (i : Fin n) :
    CertifiedFunctions.Map :=
  coordinateMap a (initialFromValue a ha M K hM hK hMK haB p hp v) M K hM hK hMK haB i

def throughCoordinate_holomorphic (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n) (i : Fin n) :
    CertifiedFunctions.Holomorphic (throughCoordinate a ha M K hM hK hMK haB p hp v i) :=
  coordinateMap_holomorphic a (initialFromValue a ha M K hM hK hMK haB p hp v) M K hM hK hMK haB i

theorem throughCoordinate_value (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n) (i : Fin n)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    (throughCoordinate a ha M K hM hK hMK haB p hp v i).eval z =
      (throughValue a ha M K hM hK hMK haB p hp v z hz).val i := rfl

theorem throughValue_normalized (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n) :
    throughValue a ha M K hM hK hMK haB p hp v p hp ≈ v :=
  localValue_initialFromValue a ha M K hM hK hMK haB p hp v

theorem throughValue_ode (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    localDerivative a (initialFromValue a ha M K hM hK hMK haB p hp v) M K hM hK hMK haB z hz ≈
      (coefficientValueMap a M K hM hK haB z hz).eval (throughValue a ha M K hM hK hMK haB p hp v z hz) :=
  localValue_ode a ha (initialFromValue a ha M K hM hK hMK haB p hp v) M K hM hK hMK haB z hz

theorem throughValue_congr (a b : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (hb : ∀ k, IsLinear (b k)) (hab : ∀ k, (a k).Equiv (b k))
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L) (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (p q : Scalar) (hpq : p.val.Equiv q.val)
    (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius L hL).val q)
    (v u : Fiber n) (hvu : v ≈ u) (z w : Scalar) (hzw : z.val.Equiv w.val)
    (hz : interior (solutionRadius K hK).val z) (hw : interior (solutionRadius L hL).val w) :
    throughValue a ha M K hM hK hMK haB p hp v z hz ≈ throughValue b hb P L hP hL hPL hbB q hq u w hw :=
  localValue_congr a b _ _ hab
    (initialFromValue_congr a b ha hb hab M K P L hM hK hP hL hMK hPL haB hbB p q hpq hp hq v u hvu)
    M K P L hM hK hP hL hMK hPL haB hbB z w hzw hz hw

/-- Exact local initial-value uniqueness at any point of this chart.
The comparison field has genuine uniform derivative errors and a value bound;
it is not required to be given by coefficients. -/
theorem throughValue_unique_uniform
    (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (g : UniformLocal.Field (n := n) (solutionRadius K hK).val)
    (hgcongr : ∀ z w hz hw, z.val.Equiv w.val → g z hz ≈ g w hw)
    (B : Rat) (hB : 0 ≤ B) (hgB : ∀ z hz, CoordinateBound (g z hz) B)
    (delta : QPos → QPos)
    (hgrem : ∀ (eps H : QPos) w z hw hz, H.val ≤ (delta eps).val →
      Small (sub z.val w.val) H.val →
      CoordinateBound (UniformLocal.remainder (coefficientValueMap a M K hM hK haB) g w z hw hz)
        (eps.val*H.val))
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) (v : Fiber n) (hgp : g p hp ≈ v)
    (z : Scalar) (hz : interior (solutionRadius K hK).val z) :
    throughValue a ha M K hM hK hMK haB p hp v z hz ≈ g z hz := by
  let zeroPoint : Scalar := ⟨zero, ofQComplex_valid _⟩
  let hzero := interior_zero (solutionRadius K hK).val (solutionRadius K hK).property
  let initial := g zeroPoint hzero
  have hcompare := fun z hz => localValue_unique_uniform a ha initial M K hM hK hMK haB g
    hgcongr (Setoid.refl _) B hB hgB delta hgrem z hz
  have hpoint : localValue a initial M K hM hK hMK haB p hp ≈ v := Setoid.trans (hcompare p hp) hgp
  have hseed : initialFromValue a ha M K hM hK hMK haB p hp v ≈ initial :=
    Setoid.trans ((localValueIso a ha M K hM hK hMK haB p hp).toValueIso.backward.congr (Setoid.symm hpoint))
      (initialFromValue_localValue a ha M K hM hK hMK haB p hp initial)
  exact Setoid.trans
    (localValue_congr a a _ initial (fun _ => ValueMap.equiv_refl _) hseed
      M K M K hM hK hM hK hMK hMK haB haB z z (equiv_refl _ z.property) hz hz) (hcompare z hz)

end ComputableAnalysis.RiemannHilbert.LocalSystem
