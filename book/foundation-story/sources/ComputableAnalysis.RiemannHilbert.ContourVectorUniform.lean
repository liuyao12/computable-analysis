import ComputableAnalysis.RiemannHilbert.ContourMatrixTaylor
import ComputableAnalysis.RiemannHilbert.DomainVectorHolomorphicLaws
import ComputableAnalysis.RiemannHilbert.DomainDerivativeOverlap

/-! Every supplied represented holomorphic vector map has an internally
computed neighborhood with a common value bound and uniform first-order
error modulus. These are derived from actual Cauchy reconstruction; they
are not additional regularity or solution hypotheses. -/
namespace ComputableAnalysis.RiemannHilbert.ConstructedVectorTaylor
open ComplexRaw FunctionTheory LocalSystem DomainFunctions LinearField
set_option autoImplicit false
variable {n : Nat}

def column (f : DomainVectorFunctions.Map n) : Field (n := 1) (m := n) f.domain :=
  fun z hz => ValueMap.ofColumns (fun _ => f.eval z hz)

theorem column_names (f : DomainVectorFunctions.Map n) (z w : Scalar) (hz : f.domain z) (hw : f.domain w) (he : z≈w) :
    (column f z hz).Equiv (column f w hw) := ValueMap.ofColumns_congr _ _ (fun _ => f.eval_congr z w hz hw he)

theorem column_entry (f : DomainVectorFunctions.Map n) (i : Fin 1) (j : Fin n) (z : Scalar) (hz : f.domain z) :
    matrixEntry (column f) i j z hz≈Fiber.coordinate (f.eval z hz) j := ValueMap.ofColumns_basis _ i j

def column_holomorphic (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f) :
    MatrixHolomorphic (column f) (vectorOpenData f hf).invariant (column_names f) :=
  fun i j => (hf.coordinates j).transfer (entryMap (column f) (vectorOpenData f hf).invariant (column_names f) i j)
    (fun _ hz => hz) ⟨hf.openDomain.radius,hf.openDomain.inside⟩
    (fun z hz => equiv_symm (column_entry f i j z hz))

variable (f : DomainVectorFunctions.Map n) (hf : DomainVectorFunctions.Holomorphic f) (b : Scalar) (hb : f.domain b)

def radius : QPos := ConstructedMatrixTaylor.radius (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb

def bound : Rat := ConstructedMatrixTaylor.bound (column f) (vectorOpenData f hf) (column_names f) b hb

def rate : QPos := ConstructedMatrixTaylor.rate (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb

theorem bound_nonneg : 0≤bound f hf b hb := ConstructedMatrixTaylor.bound_nonneg _ _ _ _ _

theorem domain_original (z : Scalar) (hz : Centered.domain b (radius f hf b hb).val z) : f.domain z :=
  ConstructedMatrixTaylor.radius_domain (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb z hz

def entry (j : Fin n) : DomainFunctions.Map :=
  ConstructedMatrixTaylor.entry (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j

def entry_holomorphic (j : Fin n) : Holomorphic (entry f hf b hb j) :=
  SeriesMatrix.entryHolomorphic b
    (ConstructedMatrixTaylor.coefficients (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb)
    (ConstructedMatrixTaylor.coefficients_valid (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb)
    (bound f hf b hb) (rate f hf b hb).val (radius f hf b hb).val (bound_nonneg f hf b hb)
    (Rat.le_of_lt (rate f hf b hb).property) (Rat.le_of_lt (radius f hf b hb).property)
    (ConstructedMatrixTaylor.coefficients_bound (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb)
    (ConstructedMatrixTaylor.radius_budget (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb) 0 j

theorem entry_agrees (j : Fin n) (z : Scalar) (hz : Centered.domain b (radius f hf b hb).val z) (ha : f.domain z) :
    (entry f hf b hb j).eval z hz≈Fiber.coordinate (f.eval z ha) j :=
  equiv_trans ((entry f hf b hb j).eval z hz).property (matrixEntry (column f) 0 j z ha).property ((f.eval z ha).property j)
    (ConstructedMatrixTaylor.entry_agrees (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j z hz ha)
    (column_entry f 0 j z ha)

theorem entry_derivative_agrees (j : Fin n) (z : Scalar) (hz : Centered.domain b (radius f hf b hb).val z) (ha : f.domain z) :
    (entry_holomorphic f hf b hb j).derivative z hz≈(hf.coordinates j).derivative z ha :=
  (entry_holomorphic f hf b hb j).derivative_equiv_on_overlap (hf.coordinates j)
    (fun w hw hwf => entry_agrees f hf b hb j w hw hwf) z hz ha

theorem value_bound (z : Scalar) (hz : Centered.domain b (radius f hf b hb).val z) (ha : f.domain z) :
    CoordinateBound (f.eval z ha) (4*bound f hf b hb) := by
  intro j
  have hs := CenteredSeries.value_bound b
    (ConstructedMatrixTaylor.coefficients (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (ConstructedMatrixTaylor.coefficients_valid (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (bound f hf b hb) (rate f hf b hb).val (radius f hf b hb).val (bound_nonneg f hf b hb)
    (Rat.le_of_lt (rate f hf b hb).property) (Rat.le_of_lt (radius f hf b hb).property)
    (ConstructedMatrixTaylor.coefficients_bound (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (ConstructedMatrixTaylor.radius_budget (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb) z hz
  exact Small.congr ((entry f hf b hb j).eval z hz).property ((f.eval z ha).property j) (entry_agrees f hf b hb j z hz ha) hs

def delta (eps : QPos) : QPos := LocalODE.derivativeDelta (bound f hf b hb) (rate f hf b hb).val
  (bound_nonneg f hf b hb) (Rat.le_of_lt (rate f hf b hb).property) eps

/-- A uniform derivative error for the original supplied vector evaluator. -/
theorem uniform_remainder (eps H : QPos) (w z : Scalar)
    (hw : Centered.domain b (radius f hf b hb).val w) (hz : Centered.domain b (radius f hf b hb).val z)
    (hwa : f.domain w) (hza : f.domain z) (hH : H.val≤(delta f hf b hb eps).val) (hzw : Small (sub z.val w.val) H.val) :
    CoordinateBound (Fiber.sub (Fiber.sub (f.eval z hza) (f.eval w hwa))
      (Fiber.scale ⟨sub z.val w.val,sub_valid z.property w.property⟩ (DomainVectorFunctions.derivative f hf w hwa))) (eps.val*H.val) := by
  intro j
  let e := entry f hf b hb j
  let he := entry_holomorphic f hf b hb j
  let d := (hf.coordinates j).derivative w hwa
  let dz : Scalar := ⟨sub z.val w.val,sub_valid z.property w.property⟩
  have hs := CenteredSeries.uniform_remainder b
    (ConstructedMatrixTaylor.coefficients (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (ConstructedMatrixTaylor.coefficients_valid (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (bound f hf b hb) (rate f hf b hb).val (radius f hf b hb).val (bound_nonneg f hf b hb)
    (Rat.le_of_lt (rate f hf b hb).property) (Rat.le_of_lt (radius f hf b hb).property)
    (ConstructedMatrixTaylor.coefficients_bound (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb 0 j)
    (ConstructedMatrixTaylor.radius_budget (column f) (vectorOpenData f hf) (column_names f) (column_holomorphic f hf) b hb) eps H w z hw hz hH hzw
  have hm : (mul (he.derivative w hw).val dz.val).Equiv (mul dz.val d.val) :=
    equiv_trans (mul_valid (he.derivative w hw).property dz.property) (mul_valid d.property dz.property) (mul_valid dz.property d.property)
      (mul_equiv (he.derivative w hw).property d.property dz.property dz.property
        (entry_derivative_agrees f hf b hb j w hw hwa) (equiv_refl _ dz.property))
      (mul_comm_equiv _ _ d.property dz.property)
  exact Small.congr (DomainFunctions.remainder_valid e w hw (he.derivative w hw) z hz)
    (sub_valid (sub_valid ((f.eval z hza).property j) ((f.eval w hwa).property j)) (mul_valid dz.property d.property))
    (FunctionTheory.sub_congr (FunctionTheory.sub_congr (entry_agrees f hf b hb j z hz hza) (entry_agrees f hf b hb j w hw hwa)) hm) hs

end ComputableAnalysis.RiemannHilbert.ConstructedVectorTaylor
