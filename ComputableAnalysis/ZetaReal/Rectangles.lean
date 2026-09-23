import ComputableAnalysis.ZetaReal.Moments

namespace ComputableAnalysis.ZetaReal
open FormalPowerSeries

/-- A finite rectangle: binomial degree below `K`, Dirichlet index below `N`. -/
def rectangle (s : Rat) (K N : Nat) : Rat :=
  sumBelow (fun k => coefficient s k*moment k N) K

private theorem chart_gap {q m : Nat} {s : Rat} (hs : InChart q m s) :
    1 ≤ (s-1)*((q : Rat)+1) := by
  have hq := Rat.natCast_nonneg (a := q)
  have hi := Rat.mul_inv_cancel ((q : Rat)+1) (by grind)
  have h := Rat.mul_le_mul_of_nonneg_right hs.1 (by grind : 0 ≤ (q : Rat)+1)
  simp only [Rat.div_def] at h
  grind only

theorem outer_term_bound {q m k : Nat} {s : Rat} (hs : InChart q m s)
    (hk : m+1 ≤ k) (N : Nat) :
    qabs (coefficient s k*moment k N) ≤
      2*((q : Rat)+1)*(magnitude s k-magnitude s (k+1)) := by
  have hd := magnitude_difference hs.2 hk
  have hm := magnitude_nonneg s k
  have hgap := chart_gap hs
  have hq := Rat.natCast_nonneg (a := q)
  have hdec := magnitude_decreasing (Rat.le_of_lt (chart_gt_one hs)) hs.2 hk
  have hdiff : 0 ≤ magnitude s k-magnitude s (k+1) := by grind
  have hu := Rat.mul_le_mul_of_nonneg_right hgap hm
  have hn := moment_nonneg k N
  have hb := moment_bound k N
  have hh : magnitude s k ≤ ((q : Rat)+1)*((k : Rat)+1)*
      (magnitude s k-magnitude s (k+1)) := by
    calc
      magnitude s k ≤ ((s-1)*magnitude s k)*((q : Rat)+1) := by grind only
      _ = _ := by rw [hd]; grind only
  have h1 := Rat.mul_le_mul_of_nonneg_right hh hn
  have h2 := Rat.mul_le_mul_of_nonneg_left hb (Rat.mul_nonneg (by grind : 0 ≤ (q : Rat)+1) hdiff)
  rw [qabs_mul, qabs_eq_self_of_nonneg hn]
  change magnitude s k*moment k N ≤ _
  grind only

/-- A summable outer tail, uniform in the finite Dirichlet cutoff. -/
theorem rectangle_outer_tail {q m K : Nat} {s : Rat} (hs : InChart q m s)
    (hK : m+1 ≤ K) (L N : Nat) :
    qabs (rectangle s (K+L) N-rectangle s K N) ≤ 2*((q : Rat)+1)*magnitude s K := by
  have all (L : Nat) :
      qabs (rectangle s (K+L) N-rectangle s K N) ≤
        2*((q : Rat)+1)*(magnitude s K-magnitude s (K+L)) := by
    induction L with
    | zero => simp [qabs]; grind
    | succ L ih =>
      have ht := outer_term_bound hs (by omega : m+1 ≤ K+L) N
      have ha := qabs_add_le (rectangle s (K+L) N-rectangle s K N)
        (coefficient s (K+L)*moment (K+L) N)
      have he : rectangle s (K+(L+1)) N-rectangle s K N =
          (rectangle s (K+L) N-rectangle s K N)+coefficient s (K+L)*moment (K+L) N := by
        unfold rectangle
        rw [show K+(L+1)=(K+L)+1 by omega, sumBelow_succ]
        grind only
      rw [he]
      rw [show K+(L+1)=K+L+1 by omega]
      grind only
  have h := all L
  have hq := Rat.natCast_nonneg (a := q)
  have hnon := Rat.mul_nonneg (by grind : 0 ≤ 2*((q : Rat)+1)) (magnitude_nonneg s (K+L))
  grind only

/-- Increasing the Dirichlet cutoff has a uniform explicit error bound. -/
theorem rectangle_inner_tail {q m N : Nat} {s : Rat} (hs : InChart q m s)
    (hN : 0 < N) (K L : Nat) :
    qabs (rectangle s K (N+L)-rectangle s K N) ≤ (K : Rat)*bound m/(N : Rat) := by
  have hn : 0 < (N : Rat) := (Rat.natCast_pos).mpr hN
  have hInv : 0 ≤ 1/(N : Rat) := by
    rw [Rat.div_def]; exact Rat.mul_nonneg (by decide) (Rat.le_of_lt (Rat.inv_pos.mpr hn))
  induction K with
  | zero => simp [rectangle, qabs]; grind
  | succ K ih =>
    have ht := moment_tail hN K L
    have hc := magnitude_bound hs K
    have h1 := Rat.mul_le_mul_of_nonneg_left ht.2 (magnitude_nonneg s K)
    have h2 := Rat.mul_le_mul_of_nonneg_right hc hInv
    have hterm : qabs (coefficient s K*(moment K (N+L)-moment K N)) ≤ bound m/(N : Rat) := by
      rw [qabs_mul, qabs_eq_self_of_nonneg ht.1]
      change magnitude s K*(moment K (N+L)-moment K N) ≤ _
      simp only [Rat.div_def] at *
      grind only
    have he : rectangle s (K+1) (N+L)-rectangle s (K+1) N =
        (rectangle s K (N+L)-rectangle s K N)+coefficient s K*(moment K (N+L)-moment K N) := by
      unfold rectangle
      rw [sumBelow_succ, sumBelow_succ]
      grind only
    have ha := qabs_add_le (rectangle s K (N+L)-rectangle s K N)
      (coefficient s K*(moment K (N+L)-moment K N))
    rw [he]
    simp only [Rat.natCast_add, Rat.div_def] at *
    grind only

end ComputableAnalysis.ZetaReal
