import ComputableAnalysis.RiemannHilbert.LocalSolutionThrough

/-! Reversible transport by actual local holomorphic solutions inside one
certified chart. Composition follows from the constructed evaluation inverses. -/
namespace ComputableAnalysis.RiemannHilbert.LocalSystem
open ComplexRaw FunctionTheory LocalODE
variable {n : Nat}

def transport (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p q : Scalar) (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q) :
    LinearIso n n :=
  (localValueIso a ha M K hM hK hMK haB p hp).inverse.followedBy
    (localValueIso a ha M K hM hK hMK haB q hq)

theorem transport_value (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p q : Scalar) (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q)
    (v : Fiber n) :
    (transport a ha M K hM hK hMK haB p q hp hq).toValueIso.forward.eval v =
      throughValue a ha M K hM hK hMK haB p hp v q hq := rfl

theorem transport_self (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p : Scalar) (hp : interior (solutionRadius K hK).val p) :
    (transport a ha M K hM hK hMK haB p p hp hp).toValueIso.forward.Equiv ValueMap.identity :=
  fun v => throughValue_normalized a ha M K hM hK hMK haB p hp v

theorem transport_solution (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p q : Scalar) (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q)
    (initial : Fiber n) :
    (transport a ha M K hM hK hMK haB p q hp hq).toValueIso.forward.eval
      (localValue a initial M K hM hK hMK haB p hp) ≈ localValue a initial M K hM hK hMK haB q hq :=
  (localValueIso a ha M K hM hK hMK haB q hq).toValueIso.forward.congr
    (initialFromValue_localValue a ha M K hM hK hMK haB p hp initial)

/-- Actual within-chart transport depends only on the two endpoints;
inserting an intermediate represented point changes no transported value. -/
theorem transport_compose (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p q r : Scalar) (hp : interior (solutionRadius K hK).val p)
    (hq : interior (solutionRadius K hK).val q) (hr : interior (solutionRadius K hK).val r) :
    ((transport a ha M K hM hK hMK haB p q hp hq).toValueIso.forward.followedBy
      (transport a ha M K hM hK hMK haB q r hq hr).toValueIso.forward).Equiv
        (transport a ha M K hM hK hMK haB p r hp hr).toValueIso.forward := by
  intro v
  let F := (localValueIso a ha M K hM hK hMK haB p hp).toValueIso
  let G := (localValueIso a ha M K hM hK hMK haB q hq).toValueIso
  let H := (localValueIso a ha M K hM hK hMK haB r hr).toValueIso
  exact H.forward.congr (G.backward_forward (F.backward.eval v))

theorem transport_reverse (a : Nat → ValueMap (Fiber n) (Fiber n)) (ha : ∀ k, IsLinear (a k))
    (M K : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hMK : 2*M ≤ K) (haB : OperatorMajorant a M K)
    (p q : Scalar) (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q) :
    (transport a ha M K hM hK hMK haB q p hq hp).toValueIso.forward.Equiv
      (transport a ha M K hM hK hMK haB p q hp hq).toValueIso.backward :=
  fun _ => Setoid.refl _

theorem transport_congr (a b : Nat → ValueMap (Fiber n) (Fiber n))
    (ha : ∀ k, IsLinear (a k)) (hb : ∀ k, IsLinear (b k)) (hab : ∀ k, (a k).Equiv (b k))
    (M K P L : Rat) (hM : 0 ≤ M) (hK : 0 ≤ K) (hP : 0 ≤ P) (hL : 0 ≤ L)
    (hMK : 2*M ≤ K) (hPL : 2*P ≤ L) (haB : OperatorMajorant a M K) (hbB : OperatorMajorant b P L)
    (p q p' q' : Scalar) (hpp' : p.val.Equiv p'.val) (hqq' : q.val.Equiv q'.val)
    (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q)
    (hp' : interior (solutionRadius L hL).val p') (hq' : interior (solutionRadius L hL).val q') :
    (transport a ha M K hM hK hMK haB p q hp hq).toValueIso.forward.Equiv
      (transport b hb P L hP hL hPL hbB p' q' hp' hq').toValueIso.forward :=
  fun v => throughValue_congr a b ha hb hab M K P L hM hK hP hL hMK hPL haB hbB
    p p' hpp' hp hp' v v (Setoid.refl _) q q' hqq' hq hq'

/-- Agreement on an open chart for every justified uniform horizontal field,
rather than an endpoint-only numerical transport assertion. -/
theorem transport_uniform_field
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
    (p q : Scalar) (hp : interior (solutionRadius K hK).val p) (hq : interior (solutionRadius K hK).val q) :
    (transport a ha M K hM hK hMK haB p q hp hq).toValueIso.forward.eval (g p hp) ≈ g q hq :=
  throughValue_unique_uniform a ha M K hM hK hMK haB g hgcongr B hB hgB delta hgrem
    p hp (g p hp) (Setoid.refl _) q hq

end ComputableAnalysis.RiemannHilbert.LocalSystem
