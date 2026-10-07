import ComputableAnalysis.ModularForms.PairedPoleChartRecognition

/-! Finite rational-box recognition of the off-pole chart, with proved eventual success. -/
namespace ComputableAnalysis.ModularForms
open ComplexRaw RiemannHilbert FunctionTheory DomainFunctions NonzeroBoxSearch

theorem nonzero_of_separated_box (z : Scalar) (N : Nat) (hs : separated (z.val.compute N)) : Nonzero z := by
  intro he
  have ho := (compareAt_overlap_iff z.val zero N N).mp (he N)
  change ((z.val.compute N).lo.re≤0 ∧ (z.val.compute N).lo.im≤0) ∧
    (0≤(z.val.compute N).hi.re ∧ 0≤(z.val.compute N).hi.im) at ho
  unfold separated at hs
  grind only

def offPolePairRecognized (z : Scalar) (n N : Nat) : Bool :=
  good (integerShiftScalar z (-((n+1:Nat):Int))) N && good (integerShiftScalar z ((n+1:Nat):Int)) N

def offPoleChartRecognized (z : Scalar) (N : Nat) : Bool :=
  good (integerShiftScalar z 0) N &&
    (List.range (4*pairedOffPoleCanonicalCutoff z)).all (fun n => offPolePairRecognized z n N)

private theorem good_nonzero (z : Scalar) (N : Nat) (h : good z N=true) : Nonzero z :=
  nonzero_of_separated_box z N (by simpa only [good,decide_eq_true_eq] using h)

theorem offPoleChartRecognized_sound (z : Scalar) (N : Nat) (h : offPoleChartRecognized z N=true) :
    pairedOffPoleDomain z := by
  have hh := Bool.and_eq_true_iff.mp h
  have ht := List.all_eq_true.mp hh.2
  have hf (L : Nat) (hL : L≤4*pairedOffPoleCanonicalCutoff z) : (pairedFiniteOffPoleMap L).domain z := by
    induction L with
    | zero => exact trivial
    | succ L ih =>
      have hp := Bool.and_eq_true_iff.mp (ht L (List.mem_range.mpr (by omega)))
      exact ⟨ih (by omega),⟨trivial,good_nonzero _ N hp.1⟩,⟨trivial,good_nonzero _ N hp.2⟩⟩
  exact pairedOffPoleAssemblyMap_domain_global (pairedOffPoleCanonicalCutoff z) z
    ⟨⟨trivial,good_nonzero _ N hh.1⟩,hf _ (Nat.le_refl _),pairedOffPoleCanonicalCutoff_interior z⟩

private theorem finite_eventually (f : Nat → Nat → Bool)
    (hf : ∀ i, ∃ M, ∀ N, M≤N → f i N=true) (L : Nat) :
    ∃ M, ∀ N, M≤N → ∀ i, i<L → f i N=true := by
  induction L with
  | zero => exact ⟨0,fun _ _ i hi => by omega⟩
  | succ L ih =>
    obtain ⟨M,hM⟩ := ih
    obtain ⟨K,hK⟩ := hf L
    refine ⟨max M K,?_⟩
    intro N hN i hi
    by_cases hil : i<L
    · exact hM N (by omega) i hil
    · have he : i=L := by omega
      subst i
      exact hK N (by omega)

theorem offPoleChartRecognized_eventually (z : Scalar) (hz : pairedOffPoleDomain z) :
    ∃ M, ∀ N, M≤N → offPoleChartRecognized z N=true := by
  have hp (n : Nat) : ∃ M, ∀ N, M≤N → offPolePairRecognized z n N=true := by
    obtain ⟨A,hA⟩ := eventually_good _ (pairedOffPoleDomain_integer_nonzero z hz (-((n+1:Nat):Int)))
    obtain ⟨B,hB⟩ := eventually_good _ (pairedOffPoleDomain_integer_nonzero z hz ((n+1:Nat):Int))
    refine ⟨max A B,?_⟩
    intro N hN
    exact Bool.and_eq_true_iff.mpr ⟨hA N (by omega),hB N (by omega)⟩
  obtain ⟨A,hA⟩ := finite_eventually (offPolePairRecognized z) hp (4*pairedOffPoleCanonicalCutoff z)
  obtain ⟨B,hB⟩ := eventually_good _ (pairedOffPoleDomain_integer_nonzero z hz 0)
  refine ⟨max A B,?_⟩
  intro N hN
  apply Bool.and_eq_true_iff.mpr
  refine ⟨hB N (by omega),?_⟩
  apply List.all_eq_true.mpr
  intro n hn
  exact hA N (by omega) n (List.mem_range.mp hn)

end ComputableAnalysis.ModularForms
