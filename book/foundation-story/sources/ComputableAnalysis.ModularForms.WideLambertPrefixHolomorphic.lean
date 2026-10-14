import ComputableAnalysis.ModularForms.WideLambertFifthDerivative
import ComputableAnalysis.ModularForms.WideWeightedLambertHolomorphic
import ComputableAnalysis.RiemannHilbert.DomainHolomorphicSums

/-! Holomorphicity of literal finite weighted Lambert prefixes. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions

def wideLambertPrefixMap (k N : Nat) : DomainFunctions.Map where
  domain := wideLambertFifthDomain
  eval q hq := ⟨ScalarSeries.block (weightedLambertTerm q (1/64) k) 0 N,
    ScalarSeries.block_valid _
      (weightedLambertTerm_valid q _ k (by decide +kernel) (by decide +kernel)
        (LocalODE.interior_bound _ q hq)) 0 N⟩
  domain_congr := wideLambertFifthDomain_openData.invariant
  eval_congr q w hq hw he := ScalarSeries.block_congr _ _
    (fun n => (wideWeightedLambertMap k n).eval_congr q w hq hw he) 0 N

/-- Each finite prefix is holomorphic with a constructed derivative. -/
def wideLambertPrefixMap_holomorphic (k : Nat) : (N : Nat) → Holomorphic (wideLambertPrefixMap k N)
  | 0 => by
    exact (constantOn_holomorphic wideLambertFifthDomain_openData ⟨zero,ofQComplex_valid _⟩).transfer
      (wideLambertPrefixMap k 0) (fun _ h => h)
      ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
      (fun _ _ => equiv_refl _ (ofQComplex_valid _))
  | N+1 => by
    exact ((wideLambertPrefixMap_holomorphic k N).sumOn (wideWeightedLambertMap_holomorphic k N) (fun _ h => h)).transfer
      (wideLambertPrefixMap k (N+1)) (fun _ h => h)
      ⟨wideLambertFifthDomain_openData.radius,wideLambertFifthDomain_openData.inside⟩
      (fun q hq => by
        simpa only [wideLambertPrefixMap, wideWeightedLambertMap, sumOn, scalarSum,
          ScalarSeries.block, Nat.zero_add] using
          equiv_refl (add ((wideLambertPrefixMap k N).eval q hq).val
            ((wideWeightedLambertMap k N).eval q hq).val)
            (add_valid ((wideLambertPrefixMap k N).eval q hq).property
              ((wideWeightedLambertMap k N).eval q hq).property))


/-- The actual prefix derivative obeys the finite sum-rule step. -/
theorem wideLambertPrefixMap_derivative_step (k N : Nat) (q : Scalar) (hq : wideLambertFifthDomain q) :
    ((wideLambertPrefixMap_holomorphic k (N+1)).derivative q hq).val.Equiv
      (add ((wideLambertPrefixMap_holomorphic k N).derivative q hq).val
        ((wideWeightedLambertMap_holomorphic k N).derivative q hq).val) := by
  exact equiv_refl _ (add_valid ((wideLambertPrefixMap_holomorphic k N).derivative q hq).property
    ((wideWeightedLambertMap_holomorphic k N).derivative q hq).property)

private theorem derivative_block_of_steps (d t : Nat → Scalar)
    (hzero : (d 0).val.Equiv zero)
    (hstep : ∀ n, (d (n+1)).val.Equiv (add (d n).val (t n).val)) (N : Nat) :
    (d N).val.Equiv (ScalarSeries.block (fun n => (t n).val) 0 N) := by
  induction N with
  | zero => exact hzero
  | succ N ih =>
    have hb : (ScalarSeries.block (fun n => (t n).val) 0 (N+1)) =
        add (ScalarSeries.block (fun n => (t n).val) 0 N) (t N).val := by
      simp only [ScalarSeries.block, Nat.zero_add]
    rw [hb]
    exact equiv_trans (d (N+1)).property (add_valid (d N).property (t N).property)
      (add_valid (ScalarSeries.block_valid _ (fun n => (t n).property) 0 N) (t N).property)
      (hstep N) (add_equiv ih (equiv_refl _ (t N).property))

/-- Exact finite sum rule for the actual weighted Lambert prefix derivatives. -/
theorem wideLambertPrefixMap_derivative (k N : Nat) (q : Scalar) (hq : wideLambertFifthDomain q) :
    ((wideLambertPrefixMap_holomorphic k N).derivative q hq).val.Equiv
      (ScalarSeries.block (fun n => ((wideWeightedLambertMap_holomorphic k n).derivative q hq).val) 0 N) := by
  exact derivative_block_of_steps
    (fun n => (wideLambertPrefixMap_holomorphic k n).derivative q hq)
    (fun n => (wideWeightedLambertMap_holomorphic k n).derivative q hq)
    (equiv_refl _ (ofQComplex_valid _))
    (fun n => wideLambertPrefixMap_derivative_step k n q hq) N

end ComputableAnalysis.ModularForms
