import ComputableAnalysis.ModularForms.PairedIntegerPoleChartOverlap

/-! Executable enumeration and rational-box recognition of integer pole disks. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions

def poleChartInteger (n : Nat) : Int :=
  if n%2=0 then ((n/2:Nat):Int) else -((n/2+1:Nat):Int)

theorem poleChartInteger_surjective (k : Int) : ∃ n, poleChartInteger n=k := by
  cases k with
  | ofNat n =>
    refine ⟨2*n,?_⟩
    have hmod : (2*n)%2=0 := by omega
    have hdiv : (2*n)/2=n := by omega
    simp [poleChartInteger,hmod,hdiv]
  | negSucc n =>
    refine ⟨2*n+1,?_⟩
    have hmod : (2*n+1)%2≠0 := by omega
    have hdiv : (2*n+1)/2=n := by omega
    simp only [poleChartInteger,hmod,hdiv,if_neg False.elim]
    omega

def poleChartRecognized (z : Scalar) (N : Nat) : Bool :=
  (List.range (N+1)).any (fun n => LocalODE.boxInside (1/4)
    (integerShiftScalar z (-(poleChartInteger n))) N)

theorem poleChartRecognized_sound (z : Scalar) (N : Nat) (h : poleChartRecognized z N=true) :
    ∃ k : Int, (pairedIntegerRiccatiExtensionMap k).domain z := by
  obtain ⟨n,hn,hgood⟩ := List.any_eq_true.mp h
  let w := integerShiftScalar z (-(poleChartInteger n))
  have hb : LocalODE.boxCoordinateBound (w.val.compute N)<(1:Rat)/4 := by
    simpa only [LocalODE.boxInside,decide_eq_true_eq] using hgood
  refine ⟨poleChartInteger n,trivial,?_⟩
  exact ⟨LocalODE.boxCoordinateBound (w.val.compute N),LocalODE.boxCoordinateBound_nonneg _,hb,
    LocalODE.small_from_box w.val w.property N⟩

theorem poleChartRecognized_eventually (k : Int) (z : Scalar)
    (hz : (pairedIntegerRiccatiExtensionMap k).domain z) :
    ∃ M, ∀ N, M≤N → poleChartRecognized z N=true := by
  obtain ⟨n,hn⟩ := poleChartInteger_surjective k
  obtain ⟨M,hM⟩ := LocalODE.eventually_boxInside (1/4) (integerShiftScalar z (-k)) (compose_outer_mem hz)
  refine ⟨max M n,?_⟩
  intro N hN
  apply List.any_eq_true.mpr
  refine ⟨n,?_,?_⟩
  · exact List.mem_range.mpr (by omega)
  · rw [hn]
    exact hM N (by omega)

end ComputableAnalysis.ModularForms
