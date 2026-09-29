import ComputableAnalysis.ZetaReal.Charts
import ComputableAnalysis.BinomialPowerPolynomial

namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- The finite approximation to `(n+1)^(-s)` uses the uniquely specified
binomial power at `z = 1-1/(n+1)`. -/
def inversePowerApprox (s : Rat) (n K : Nat) : Rat :=
  reciprocal n^2*powerPolynomial s K (node n)

/-- Exact finite interchange: the rectangle really is a Dirichlet partial sum
with every power evaluated to the same binomial degree. -/
theorem rectangle_dirichlet (s : Rat) (K N : Nat) :
    rectangle s K N=sumBelow (fun n => inversePowerApprox s n K) N := by
  induction N with
  | zero =>
    unfold rectangle moment
    have he : (fun k => coefficient s k*sumBelow (kernel k) 0)=(fun _ => (0 : Rat)) := by funext k; simp
    rw [he]
    induction K <;> simp_all [sumBelow_succ] <;> grind
  | succ N ih =>
    have he : rectangle s K (N+1)=rectangle s K N+inversePowerApprox s N K := by
      unfold rectangle moment inversePowerApprox powerPolynomial
      calc
        _ = sumBelow (fun k => coefficient s k*sumBelow (kernel k) N+reciprocal N^2*(coefficient s k*node N^k)) K := by
          apply sumBelow_congr
          intro k _
          rw [sumBelow_succ]
          unfold kernel; grind only
        _ = _ := by rw [sumBelow_add, sumBelow_mul]
    rw [he, ih, sumBelow_succ]

theorem inversePowerApprox_integer (p n K : Nat) (hK : p < K) :
    inversePowerApprox ((p : Rat)+2) n K=DirichletSeries.zetaNatTerm (p+2) n := by
  rw [inversePowerApprox, powerPolynomial_integer p K hK]
  have hn : (n : Rat)+1 ≠ 0 := by have := Rat.natCast_nonneg (a := n); grind
  have he : 1-node n=reciprocal n := by unfold node; grind only
  rw [he]
  unfold reciprocal DirichletSeries.zetaNatTerm
  simp only [Rat.natCast_add, Rat.div_def, Rat.one_mul]
  change (((n : Rat)+1)⁻¹)^2*(((n : Rat)+1)⁻¹)^p = (((n : Rat)+1)^(p+2))⁻¹
  clear hK
  induction p with
  | zero =>
    change ((n : Rat)+1)⁻¹^2*((n : Rat)+1)⁻¹^0=(((n : Rat)+1)^2)⁻¹
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul, Rat.mul_one]
    rw [Rat.inv_mul_rev]
  | succ p ih =>
    rw [show p+1+2=(p+2)+1 by omega, Rat.pow_succ ((n : Rat)+1) (p+2), Rat.pow_succ (((n : Rat)+1)⁻¹) p, Rat.inv_mul_rev]
    rw [← ih]
    grind only

theorem rectangle_integer (p K N : Nat) (hK : p < K) :
    rectangle ((p : Rat)+2) K N=DirichletSeries.zetaNatPartial (p+2) N := by
  rw [rectangle_dirichlet]
  induction N with
  | zero => rfl
  | succ N ih => rw [sumBelow_succ, ih, inversePowerApprox_integer p N K hK]; rfl

/-- Compatibility with the pre-existing integer Dirichlet-series evaluator. -/
theorem raw_integer_equiv {q m : Nat} (hq : 0 < q) (p : Nat)
    (hs : InChart q m ((p : Rat)+2)) :
    (raw q m hq ((p : Rat)+2)).Equiv (DirichletSeries.zetaNatRaw (p+2)) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  apply (RealRaw.compareAt_overlap_iff _ _ n n).2
  obtain ⟨K,N,h⟩ := raw_contains_rectangles hq hs n
  have hrect := h (max K (p+1)) (max N n) (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  rw [rectangle_integer p _ _ (by omega)] at hrect
  have hnest := DirichletSeries.zetaNatInterval_nested (p+2) (by omega) n (max N n) (Nat.le_max_right _ _)
  have hord := DirichletSeries.zetaNatInterval_ordered (p+2) (max N n)
  change (raw q m hq ((p : Rat)+2)).compute n |>.Overlaps (DirichletSeries.zetaNatInterval (p+2) n)
  exact ⟨Rat.le_trans hrect.1 (Rat.le_trans hord hnest.2.2), Rat.le_trans hnest.1 hrect.2⟩

end ComputableAnalysis.ZetaReal
