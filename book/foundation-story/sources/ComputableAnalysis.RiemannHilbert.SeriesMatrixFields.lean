import ComputableAnalysis.RiemannHilbert.CenteredSeriesEstimates
import ComputableAnalysis.RiemannHilbert.EntrywiseUniformEstimates

/-! Actual finite rectangular matrix series, with constructed holomorphic
entries, their actual derivative operator, uniform value and derivative
bounds, and uniform first-order errors. No operator error is assumed. -/
namespace ComputableAnalysis.RiemannHilbert.SeriesMatrix
open ComplexRaw FunctionTheory LocalODE LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n m : Nat}
variable (p : Scalar) (c : Fin n → Fin m → Nat → ComplexRaw)
    (hc : ∀ i j k, (c i j k).Valid) (C K R : Rat)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hb : ∀ i j k, Small (c i j k) (C*K^k)) (hl : 8*K*R ≤ (1 : Rat)/2)

def entry (i : Fin n) (j : Fin m) := CenteredSeries.function p (c i j) (hc i j) C K R hC hK hR (hb i j) hl

def entryHolomorphic (i : Fin n) (j : Fin m) := CenteredSeries.holomorphic p (c i j) (hc i j) C K R hC hK hR (hb i j) hl

def field : Field (n := n) (m := m) (Centered.domain p R) := fun z hz =>
  ValueMap.ofColumns (fun i => ⟨fun j => ((entry p c hc C K R hC hK hR hb hl i j).eval z hz).val,
    fun j => ((entry p c hc C K R hC hK hR hb hl i j).eval z hz).property⟩)

def slope : Field (n := n) (m := m) (Centered.domain p R) := fun z hz =>
  ValueMap.ofColumns (fun i => ⟨fun j => ((entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative z hz).val,
    fun j => ((entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative z hz).property⟩)

def openData : ScalarTopology.OpenData (Centered.domain p R) := CenteredSeries.openData p
  (fun _ => zero) (fun _ => ofQComplex_valid _) 0 K R (Rat.le_refl) hK hR
  (fun _ => Small.zero (by rw [Rat.zero_mul]; exact Rat.le_refl)) hl

theorem field_linear (z : Scalar) (hz : Centered.domain p R z) : IsLinear (field p c hc C K R hC hK hR hb hl z hz) :=
  ValueMap.ofColumns_linear _

theorem slope_linear (z : Scalar) (hz : Centered.domain p R z) : IsLinear (slope p c hc C K R hC hK hR hb hl z hz) :=
  ValueMap.ofColumns_linear _

theorem field_names (z w : Scalar) (hz : Centered.domain p R z) (hw : Centered.domain p R w) (he : z≈w) :
    (field p c hc C K R hC hK hR hb hl z hz).Equiv (field p c hc C K R hC hK hR hb hl w hw) :=
  ValueMap.ofColumns_congr _ _ (fun i j => (entry p c hc C K R hC hK hR hb hl i j).eval_congr z w hz hw he)

theorem slope_names (z w : Scalar) (hz : Centered.domain p R z) (hw : Centered.domain p R w) (he : z≈w) :
    (slope p c hc C K R hC hK hR hb hl z hz).Equiv (slope p c hc C K R hC hK hR hb hl w hw) :=
  ValueMap.ofColumns_congr _ _ (fun i j => (entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative_congr z w hz hw he)

theorem field_entry (i : Fin n) (j : Fin m) (z : Scalar) (hz : Centered.domain p R z) :
    matrixEntry (field p c hc C K R hC hK hR hb hl) i j z hz ≈ (entry p c hc C K R hC hK hR hb hl i j).eval z hz :=
  ValueMap.ofColumns_basis _ i j

theorem slope_entry (i : Fin n) (j : Fin m) (z : Scalar) (hz : Centered.domain p R z) :
    matrixEntry (slope p c hc C K R hC hK hR hb hl) i j z hz ≈ (entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative z hz :=
  ValueMap.ofColumns_basis _ i j

def holomorphic : MatrixHolomorphic (field p c hc C K R hC hK hR hb hl)
    (openData p K R hK hR hl).invariant (field_names p c hc C K R hC hK hR hb hl) := fun i j =>
  (entryHolomorphic p c hc C K R hC hK hR hb hl i j).transfer
    (entryMap (field p c hc C K R hC hK hR hb hl) (openData p K R hK hR hl).invariant
      (field_names p c hc C K R hC hK hR hb hl) i j)
    (fun _ hz => hz) ⟨(openData p K R hK hR hl).radius,(openData p K R hK hR hl).inside⟩
    (fun z hz => equiv_symm (field_entry p c hc C K R hC hK hR hb hl i j z hz))

theorem actual_derivative (z : Scalar) (hz : Centered.domain p R z) :
    (derivativeField (holomorphic p c hc C K R hC hK hR hb hl) z hz).Equiv
      (slope p c hc C K R hC hK hR hb hl z hz) :=
  ValueMap.ofColumns_congr _ _ (fun i j => equiv_refl _
    ((entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative z hz).property)

def valueBound (n : Nat) (C : Rat) : Rat := 2*(n : Rat)*(4*C)

theorem valueBound_nonneg (n : Nat) (C : Rat) (hC : 0 ≤ C) : 0 ≤ valueBound n C :=
  Rat.mul_nonneg (Rat.mul_nonneg (by decide) Rat.natCast_nonneg) (Rat.mul_nonneg (by decide) hC)

theorem field_bound (z : Scalar) (hz : Centered.domain p R z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((field p c hc C K R hC hK hR hb hl z hz).eval x) (valueBound n C*E) :=
  operator_bound_from_entries _ (field_linear p c hc C K R hC hK hR hb hl) (4*C) (Rat.mul_nonneg (by decide) hC)
    (fun z hz i j => Small.congr ((entry p c hc C K R hC hK hR hb hl i j).eval z hz).property
      ((matrixEntry (field p c hc C K R hC hK hR hb hl) i j z hz).property)
      (equiv_symm (field_entry p c hc C K R hC hK hR hb hl i j z hz))
      (CenteredSeries.value_bound p (c i j) (hc i j) C K R hC hK hR (hb i j) hl z hz)) z hz E hE x hx

theorem slope_bound (z : Scalar) (hz : Centered.domain p R z) (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound ((slope p c hc C K R hC hK hR hb hl z hz).eval x) (valueBound n (C*K)*E) :=
  operator_bound_from_entries _ (slope_linear p c hc C K R hC hK hR hb hl) (4*(C*K))
    (Rat.mul_nonneg (by decide) (Rat.mul_nonneg hC hK))
    (fun z hz i j => Small.congr ((entryHolomorphic p c hc C K R hC hK hR hb hl i j).derivative z hz).property
      ((matrixEntry (slope p c hc C K R hC hK hR hb hl) i j z hz).property)
      (equiv_symm (slope_entry p c hc C K R hC hK hR hb hl i j z hz))
      (CenteredSeries.derivative_bound p (c i j) (hc i j) C K R hC hK hR (hb i j) hl z hz)) z hz E hE x hx

def delta (n : Nat) (C K : Rat) (hC : 0 ≤ C) (hK : 0 ≤ K) (eps : QPos) : QPos :=
  derivativeDelta C K hC hK (entryError n eps)

theorem entry_remainder (eps H : QPos) (w z : Scalar) (hw : Centered.domain p R w) (hz : Centered.domain p R z)
    (hH : H.val ≤ (derivativeDelta C K hC hK eps).val) (hzw : Small (sub z.val w.val) H.val) (i : Fin n) (j : Fin m) :
    Small ((operatorRemainder (field p c hc C K R hC hK hR hb hl) (slope p c hc C K R hC hK hR hb hl)
      w z hw hz (Fiber.basis i)).val j) (eps.val*H.val) := by
  let f := entry p c hc C K R hC hK hR hb hl i j
  let h := entryHolomorphic p c hc C K R hC hK hR hb hl i j
  let G := field p c hc C K R hC hK hR hb hl
  let DG := slope p c hc C K R hC hK hR hb hl
  let d := h.derivative w hw
  let dz : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  have hs : Small (DomainFunctions.remainder f w hw d z hz) (eps.val*H.val) :=
    CenteredSeries.uniform_remainder p (c i j) (hc i j) C K R hC hK hR (hb i j) hl eps H w z hw hz hH hzw
  have hm : (mul d.val dz.val).Equiv (mul dz.val (matrixEntry DG i j w hw).val) :=
    equiv_trans (mul_valid d.property dz.property) (mul_valid dz.property d.property)
      (mul_valid dz.property (matrixEntry DG i j w hw).property)
      (mul_comm_equiv _ _ d.property dz.property)
      (mul_equiv dz.property dz.property d.property (matrixEntry DG i j w hw).property
        (equiv_refl _ dz.property) (equiv_symm (slope_entry p c hc C K R hC hK hR hb hl i j w hw)))
  apply Small.congr (DomainFunctions.remainder_valid f w hw d z hz)
    ((operatorRemainder G DG w z hw hz (Fiber.basis i)).property j) _ hs
  exact FunctionTheory.sub_congr
    (FunctionTheory.sub_congr (equiv_symm (field_entry p c hc C K R hC hK hR hb hl i j z hz))
      (equiv_symm (field_entry p c hc C K R hC hK hR hb hl i j w hw)))
    hm

theorem uniform_remainder (eps H : QPos) (w z : Scalar) (hw : Centered.domain p R w) (hz : Centered.domain p R z)
    (hH : H.val ≤ (delta n C K hC hK eps).val) (hzw : Small (sub z.val w.val) H.val)
    (E : Rat) (hE : 0 ≤ E) (x : Fiber n) (hx : CoordinateBound x E) :
    CoordinateBound (operatorRemainder (field p c hc C K R hC hK hR hb hl) (slope p c hc C K R hC hK hR hb hl)
      w z hw hz x) ((eps.val*H.val)*E) :=
  operator_uniform_remainder_from_entries _ _ (field_linear p c hc C K R hC hK hR hb hl)
    (slope_linear p c hc C K R hC hK hR hb hl) (derivativeDelta C K hC hK)
    (entry_remainder p c hc C K R hC hK hR hb hl) eps H w z hw hz hH hzw E hE x hx

theorem field_agrees (q : Scalar) (d : Fin n → Fin m → Nat → ComplexRaw) (hd : ∀ i j k, (d i j k).Valid)
    (D L S : Rat) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hdb : ∀ i j k, Small (d i j k) (D*L^k)) (hls : 8*L*S ≤ (1 : Rat)/2)
    (hpq : p≈q) (hcd : ∀ i j k, (c i j k).Equiv (d i j k)) (z w : Scalar)
    (hz : Centered.domain p R z) (hw : Centered.domain q S w) (hzw : z≈w) :
    (field p c hc C K R hC hK hR hb hl z hz).Equiv (field q d hd D L S hD hL hS hdb hls w hw) :=
  ValueMap.ofColumns_congr _ _ (fun i j => CenteredSeries.value_agrees p (c i j) (hc i j) C K R hC hK hR (hb i j) hl
    q (d i j) (hd i j) D L S hD hL hS (hdb i j) hls hpq (hcd i j) z w hz hw hzw)

theorem slope_agrees (q : Scalar) (d : Fin n → Fin m → Nat → ComplexRaw) (hd : ∀ i j k, (d i j k).Valid)
    (D L S : Rat) (hD : 0 ≤ D) (hL : 0 ≤ L) (hS : 0 ≤ S)
    (hdb : ∀ i j k, Small (d i j k) (D*L^k)) (hls : 8*L*S ≤ (1 : Rat)/2)
    (hpq : p≈q) (hcd : ∀ i j k, (c i j k).Equiv (d i j k)) (z w : Scalar)
    (hz : Centered.domain p R z) (hw : Centered.domain q S w) (hzw : z≈w) :
    (slope p c hc C K R hC hK hR hb hl z hz).Equiv (slope q d hd D L S hD hL hS hdb hls w hw) :=
  ValueMap.ofColumns_congr _ _ (fun i j => CenteredSeries.derivative_agrees p (c i j) (hc i j) C K R hC hK hR (hb i j) hl
    q (d i j) (hd i j) D L S hD hL hS (hdb i j) hls hpq (hcd i j) z w hz hw hzw)

end ComputableAnalysis.RiemannHilbert.SeriesMatrix
