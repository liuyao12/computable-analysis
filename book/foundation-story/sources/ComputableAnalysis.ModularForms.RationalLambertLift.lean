import ComputableAnalysis.ModularForms.RationalLambertArithmetic
import ComputableAnalysis.ModularForms.RationalLambertBounds
import ComputableAnalysis.ModularForms.WideLambertFifthDerivative
import ComputableAnalysis.RiemannHilbert.BoxApproximation
import ComputableAnalysis.RiemannHilbert.DomainDerivativeBounds

/-! Irrational nome-chart evaluations derived from exact rational Lambert
prefixes. The schedule depends only on rational input boxes and fixed bounds. -/
namespace ComputableAnalysis.ModularForms.RationalLambert
open ComplexRaw FunctionTheory RiemannHilbert DomainFunctions
set_option maxHeartbeats 1000000

def inputRadius (q : Scalar) (hq : wideLambertFifthDomain q) (n : Nat) : QPos :=
  minRadius (LocalODE.interiorRadius (1/64) q hq)
    (minRadius ⟨1,by decide +kernel⟩ (divideRadius (RepresentedCauchySum.error n) ⟨139264,by decide +kernel⟩))

def sampleStage (q : Scalar) (hq : wideLambertFifthDomain q) (n : Nat) : Nat :=
  PrecisionSearch.stage q.val q.property (inputRadius q hq n)
def samplePoint (q : Scalar) (hq : wideLambertFifthDomain q) (n : Nat) : QComplex :=
  (q.val.compute (sampleStage q hq n)).center

theorem sample_close (q : Scalar) (hq : wideLambertFifthDomain q) (n : Nat) :
    Small (sub (ofQComplex (samplePoint q hq n)) q.val) (inputRadius q hq n).val := by
  have h := PrecisionSearch.stage_spec q.val q.property (inputRadius q hq n)
  exact RepresentedCauchySum.small_sub_symm _ _ _ (BoxApproximation.center_error q (sampleStage q hq n)
    (inputRadius q hq n).val (Rat.le_of_lt (inputRadius q hq n).property) h.1 h.2)

theorem sample_inside (q : Scalar) (hq : wideLambertFifthDomain q) (n : Nat) :
    wideLambertFifthDomain (point (samplePoint q hq n)) :=
  LocalODE.interiorRadius_inside (1/64) q hq _ ((sample_close q hq n).mono (minRadius_left _ _))

def sampledPrefix (q : Scalar) (hq : wideLambertFifthDomain q) (k n : Nat) : ComplexRaw :=
  ofQComplex (finitePrefix (samplePoint q hq n) k n)

theorem input_error (q : Scalar) (hq : wideLambertFifthDomain q) (k n : Nat) :
    Small (sub (comparison (point (samplePoint q hq n)) (LocalODE.interior_bound _ _ (sample_inside q hq n)) k).val
      (comparison q (LocalODE.interior_bound _ _ hq) k).val) (RepresentedCauchySum.error n).val := by
  have hr := minRadius_right (LocalODE.interiorRadius (1/64) q hq)
    (minRadius (⟨1,by decide +kernel⟩ : QPos) (divideRadius (RepresentedCauchySum.error n) ⟨139264,by decide +kernel⟩))
  have h1 := Rat.le_trans hr (minRadius_left (⟨1,by decide +kernel⟩ : QPos) _)
  have hd := Rat.le_trans hr (minRadius_right (⟨1,by decide +kernel⟩ : QPos) _)
  have hb := difference_bound q (point (samplePoint q hq n)) (LocalODE.interior_bound _ _ hq)
    (LocalODE.interior_bound _ _ (sample_inside q hq n)) k (inputRadius q hq n).val
    (Rat.le_of_lt (inputRadius q hq n).property) h1 (sample_close q hq n)
  apply hb.mono
  have hm := Rat.mul_le_mul_of_nonneg_left hd (by decide +kernel : (0:Rat)≤139264)
  rw [divideRadius_identity (RepresentedCauchySum.error n) (⟨139264,by decide +kernel⟩ : QPos)] at hm
  exact hm

def error (n : Nat) : Rat := 8*((1:Rat)/2)^n+(RepresentedCauchySum.error n).val

theorem error_shrinks : ShrinksToZero error :=
  RepresentedCauchySum.sum_shrinks _ _
    (by simpa only [show (4:Rat)*2=8 by decide +kernel] using
      LocalODE.tail_bound_shrinks 2 (1/2) (by decide +kernel) (by decide +kernel) (by decide +kernel))
    RepresentedCauchySum.error_shrinks

theorem error_antitone (m n : Nat) (hmn : m≤n) : error n≤error m := by
  have hp : ∀ d : Nat, ((1:Rat)/2)^(m+d)≤((1:Rat)/2)^m := by
    intro d
    induction d with
    | zero => simp only [Nat.add_zero]; exact Rat.le_refl
    | succ d ih =>
      rw [Nat.add_succ,Rat.pow_succ]
      have hb := Rat.mul_le_mul_of_nonneg_left (by decide +kernel : (1/2:Rat)≤1)
        (Rat.pow_nonneg (n := m+d) (by decide +kernel : (0:Rat)≤1/2))
      exact Rat.le_trans (by simpa only [Rat.mul_one] using hb) ih
  have hb := hp (n-m)
  rw [Nat.add_sub_cancel' hmn] at hb
  exact rat_add_le_add (Rat.mul_le_mul_of_nonneg_left hb (by decide +kernel))
    (RepresentedCauchySum.error_antitone m n hmn)

theorem comparison_close (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat)
    (hk : k=1 ∨ k=3 ∨ k=5) (n : Nat) :
    Small (sub (comparison q (LocalODE.interior_bound _ _ hq) k).val (sampledPrefix q hq k n)) (error n) := by
  let p := point (samplePoint q hq n)
  let hp := LocalODE.interior_bound (1/64) p (sample_inside q hq n)
  have ht := comparison_tail p hp k hk n
  have he := FunctionTheory.sub_congr (equiv_refl _ (comparison p hp k).property)
    (prefix_agrees (samplePoint q hq n) hp k n)
  have ht' := Small.congr (sub_valid (comparison p hp k).property
    (ScalarSeries.block_valid _ (weightedLambertTerm_valid p (1/64) k (by decide +kernel) (by decide +kernel) hp) 0 n))
    (sub_valid (comparison p hp k).property (ofQComplex_valid _)) he ht
  have hb := triangle _ _ _ (comparison q (LocalODE.interior_bound _ _ hq) k).property (comparison p hp k).property
    (ofQComplex_valid _) _ _ (RepresentedCauchySum.small_sub_symm _ _ _ (input_error q hq k n)) ht'
  apply hb.mono
  dsimp [error]
  grind only

def value (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat) : ComplexRaw :=
  RepresentedCauchySum.value (sampledPrefix q hq k) (fun _ => ofQComplex_valid _) (fun n => 2*error n)

theorem prefix_cauchy (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5)
    (m n : Nat) (hmn : m≤n) : Small (sub (sampledPrefix q hq k n) (sampledPrefix q hq k m)) (2*error m) := by
  have hb := triangle _ _ _ (ofQComplex_valid _) (comparison q (LocalODE.interior_bound _ _ hq) k).property
    (ofQComplex_valid _) _ _ (RepresentedCauchySum.small_sub_symm _ _ _ (comparison_close q hq k hk n))
    (comparison_close q hq k hk m)
  exact hb.mono (by have := error_antitone m n hmn; grind only)

theorem value_valid (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) :
    (value q hq k).Valid := RepresentedCauchySum.value_valid _ _ _
      (RepresentedCauchySum.twice_shrinks _ error_shrinks) (prefix_cauchy q hq k hk)

theorem value_agrees (q : Scalar) (hq : wideLambertFifthDomain q) (k : Nat) (hk : k=1 ∨ k=3 ∨ k=5) :
    (value q hq k).Equiv (comparison q (LocalODE.interior_bound _ _ hq) k).val := by
  apply SeriesLimitLaws.equiv_of_small_sub_zero
  apply SeriesLimitLaws.small_closed _ 0 (fun n => 3*error n)
    (SeriesLimitLaws.shrinks_scale _ error_shrinks 3 (by decide +kernel))
  intro n
  have hv := RepresentedCauchySum.value_close_prefix (sampledPrefix q hq k) (fun _ => ofQComplex_valid _)
    (fun n => 2*error n) (prefix_cauchy q hq k hk) n
  have hb := triangle _ _ _ (value_valid q hq k hk) (ofQComplex_valid _)
    (comparison q (LocalODE.interior_bound _ _ hq) k).property _ _ hv
    (RepresentedCauchySum.small_sub_symm _ _ _ (comparison_close q hq k hk n))
  exact hb.mono (by grind only)

end ComputableAnalysis.ModularForms.RationalLambert
