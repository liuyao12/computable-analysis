import ComputableAnalysis.IntegralSpecification
import ComputableAnalysis.Differential

/-!
# FTC for any supplied integral

The endpoint function and integral are independently supplied represented
computations. Finite local derivative-order evidence gives the endpoint law
by telescoping and the integral specification. No integral construction is a
hypothesis of the uniqueness proof, and no endpoint identity is assumed.
-/
namespace ComputableAnalysis
namespace Integral

/-- The local mean-value inequalities needed by FTC. These compare a
derivative's constant bounds with finite endpoint increments on a rational
cell; they say nothing about an integral or a quadrature algorithm. -/
structure CellDerivativeBounds (f : FunctionOnInterval) (P : Rat → RealRaw) : Prop where
  valid : ∀ x, inDomainInterval f.lower f.upper x → (P x).Valid
  lower : ∀ (u v l : Rat), f.lower ≤ u → u ≤ v → v ≤ f.upper →
    (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
      ∀ n, l ≤ (f.compute x hx n).hi) →
    (RealRaw.ofRat ((v-u)*l)).Le (P v-P u)
  upper : ∀ (u v r : Rat), f.lower ≤ u → u ≤ v → v ≤ f.upper →
    (∀ x (hx : inDomainInterval f.lower f.upper x), u ≤ x → x ≤ v →
      ∀ n, (f.compute x hx n).lo ≤ r) →
    (P v-P u).Le (RealRaw.ofRat ((v-u)*r))

private theorem telescope_bounds (v : Nat → RealRaw) (l u : Nat → Rat)
    (N : Nat) (hv : ∀ k, k ≤ N → (v k).Valid)
    (hl : ∀ k, k < N → (RealRaw.ofRat (l k)).Le (v (k+1)-v k))
    (hu : ∀ k, k < N → (v (k+1)-v k).Le (RealRaw.ofRat (u k))) :
    (RealRaw.ofRat (rectangleSum l N)).Le (v N-v 0) ∧
      (v N-v 0).Le (RealRaw.ofRat (rectangleSum u N)) := by
  induction N with
  | zero =>
    have h := RealRaw.sub_self_equiv_zero (hv 0 (by omega))
    have hvalid := RealRaw.sub_valid (hv 0 (by omega)) (hv 0 (by omega))
    exact ⟨RealRaw.le_of_equiv (RealRaw.ofRat_valid 0) hvalid
      (RealRaw.equiv_symm h), RealRaw.le_of_equiv hvalid (RealRaw.ofRat_valid 0) h⟩
  | succ N ih =>
    have hprev := ih (fun k hk => hv k (by omega))
      (fun k hk => hl k (by omega)) (fun k hk => hu k (by omega))
    have haddl := RealRaw.le_add_le_add hprev.1 (hl N (by omega))
    have haddu := RealRaw.le_add_le_add hprev.2 (hu N (by omega))
    have ht := RealRaw.sub_add_sub_cancel_middle_equiv
      (hv 0 (by omega)) (hv N (by omega)) (hv (N+1) (by omega))
    have hsum := RealRaw.add_valid
      (RealRaw.sub_valid (hv N (by omega)) (hv 0 (by omega)))
      (RealRaw.sub_valid (hv (N+1) (by omega)) (hv N (by omega)))
    have hend := RealRaw.sub_valid (hv (N+1) (by omega)) (hv 0 (by omega))
    constructor
    · exact RealRaw.le_trans hsum haddl (RealRaw.le_of_equiv hsum hend ht)
    · exact RealRaw.le_trans hsum
        (RealRaw.le_of_equiv hend hsum (RealRaw.equiv_symm ht)) haddu

/-- Every finite rectangle test bounds the endpoint difference. -/
theorem CellDerivativeBounds.encloses {f : FunctionOnInterval} {P : Rat → RealRaw}
    (hP : CellDerivativeBounds f P) (B : Bounds f) :
    B.Encloses (P f.upper-P f.lower) := by
  have h := telescope_bounds (fun k => P (B.partition.point k))
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.lower k)
    (fun k => (B.partition.point (k+1)-B.partition.point k)*B.upper k)
    B.partition.pieces
    (fun k hk => hP.valid _ (B.partition.point_in_bounds hk))
    (by
      intro k hk
      let C := B.partition.cell k hk
      exact hP.lower C.lower C.upper (B.lower k) C.lower_mem C.ordered C.upper_mem
        (fun x hx hxl hxu n => B.lower_le k hk x ⟨hxl, hxu⟩ n))
    (by
      intro k hk
      let C := B.partition.cell k hk
      exact hP.upper C.lower C.upper (B.upper k) C.lower_mem C.ordered C.upper_mem
        (fun x hx hxl hxu n => B.upper_ge k hk x ⟨hxl, hxu⟩ n))
  rw [B.partition.left_endpoint, B.partition.right_endpoint] at h
  intro n
  exact ⟨h.1 0 n, h.2 n 0⟩

/-- FTC is a law about any witness of the integral definition. There is no
chosen quadrature, monotonicity decomposition, or integral-existence premise. -/
theorem HasIntegral.ftc {f : FunctionOnInterval} {P : Rat → RealRaw} {I : RealRaw}
    (hI : HasIntegral f I) (hP : CellDerivativeBounds f P) :
    I.Equiv (P f.upper-P f.lower) :=
  equiv_of_bounds hI.tight hI.bounds hP.encloses

/-- Existence is a separate corollary: local derivative order plus tight
integrand bounds certifies the actual endpoint computation as an integral. -/
theorem CellDerivativeBounds.hasIntegral {f : FunctionOnInterval} {P : Rat → RealRaw}
    (hP : CellDerivativeBounds f P) (hab : f.lower ≤ f.upper)
    (htight : HasTightBounds f) : HasIntegral f (P f.upper-P f.lower) :=
  ⟨RealRaw.sub_valid (hP.valid _ ⟨hab, Rat.le_refl⟩)
    (hP.valid _ ⟨Rat.le_refl, hab⟩), hP.encloses, htight⟩

end Integral
end ComputableAnalysis
