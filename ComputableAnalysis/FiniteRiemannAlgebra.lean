import ComputableAnalysis.Calculus

/-! Shared finite sums and telescoping algebra. Neither proof of the cosine
integral is used here, nor are derivative or curvature assumptions. -/
namespace ComputableAnalysis
namespace FiniteRiemannAlgebra

def sum (f : Nat -> Rat) (n : Nat) : Rat :=
  ratListSum ((List.range n).map f)

theorem sum_zero (f : Nat -> Rat) : sum f 0 = 0 := rfl

theorem sum_succ (f : Nat -> Rat) (n : Nat) :
    sum f (n+1) = sum f n + f n := by
  simp only [sum, List.range_succ, List.map_append, ratListSum_append,
    List.map_cons, List.map_nil, ratListSum]
  grind

theorem finiteRawSum_lo (xs : List RealRaw) (q : Nat) :
    ((Integral.finiteRawSum xs).compute q).lo =
      ratListSum (xs.map (fun X => (X.compute q).lo)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (x.compute q).lo + ((Integral.finiteRawSum xs).compute q).lo = _
      simpa only [List.map_cons, ratListSum] using congrArg (fun z => (x.compute q).lo+z) ih

theorem finite_eventually (P : Nat -> Nat -> Prop) (m : Nat)
    (h : ∀ i, i < m -> ∃ N, ∀ n, N <= n -> P i n) :
    ∃ N, ∀ n, N <= n -> ∀ i, i < m -> P i n := by
  induction m with
  | zero => exact ⟨0, by intros; omega⟩
  | succ m ih =>
      obtain ⟨N, hN⟩ := ih (fun i hi => h i (by omega))
      obtain ⟨M, hM⟩ := h m (by omega)
      refine ⟨max N M, ?_⟩
      intro n hn i hi
      by_cases he : i = m
      · subst i
        exact hM n (by omega)
      · exact hN n (by omega) i (by omega)

/-- The finite FTC estimate is just a telescope plus the triangle inequality. -/
theorem telescope_bound (s c : Nat -> Rat) (h p e : Rat) (m : Nat)
    (hc : ∀ i, i < m -> qabs (s (i+1)-s i-h*(p*c i)) <= e) :
    qabs (s m-s 0-p*sum (fun i => h*c i) m) <= (m : Rat)*e := by
  induction m with
  | zero =>
      simp only [sum_zero, Rat.mul_zero, Rat.sub_self, show ((0 : Nat) : Rat) = (0 : Rat) by decide +kernel,
        Rat.zero_mul]
      decide +kernel
  | succ m ih =>
      have hm := ih (fun i hi => hc i (by omega))
      have hi := hc m (by omega)
      rw [sum_succ]
      have heq : s (m+1)-s 0-p*(sum (fun i => h*c i) m+h*c m) =
          (s m-s 0-p*sum (fun i => h*c i) m)+(s (m+1)-s m-h*(p*c m)) := by
        grind
      rw [heq]
      have ht := qabs_add_le (s m-s 0-p*sum (fun i => h*c i) m)
        (s (m+1)-s m-h*(p*c m))
      have hcast : ((m+1 : Nat) : Rat) = (m : Rat)+1 := by simp
      rw [hcast]
      grind


def leftSum (D : Rat -> RealRaw) (a b : Rat) (m : Nat) : RealRaw :=
  Integral.finiteRawSum ((List.range m).map (fun i =>
    RealRaw.scaleRat (mesh a b m) (D (leftPoint a b m i))))

theorem leftSum_lo (D : Rat -> RealRaw) {a b : Rat}
    (hab : a <= b) (m : Nat) (hm : 0 < m) (n : Nat) :
    ((leftSum D a b m).compute n).lo =
      sum (fun i => mesh a b m * ((D (leftPoint a b m i)).compute n).lo) m := by
  have hh := mesh_nonneg_of_le hm hab
  simp only [leftSum, finiteRawSum_lo, List.map_map, Function.comp_def, sum,
    RealRaw.scaleRat, RealRaw.scaleRatCompute, if_pos hh]

theorem grid_mem {A B a b : Rat}
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    {m i : Nat} (hm : 0 < m) (hi : i <= m) :
    inDomainInterval A B (leftPoint a b m i) := by
  have hl := leftPoint_monotone (a := a) (b := b) hm hab (Nat.zero_le i)
  have hu := leftPoint_monotone (a := a) (b := b) hm hab hi
  rw [leftPoint_zero] at hl
  rw [leftPoint_endpoint hm] at hu
  exact ⟨Rat.le_trans ha.1 hl, Rat.le_trans hu hb.2⟩

theorem leftSum_valid (D : Rat -> RealRaw) {A B a b : Rat}
    (hD : ∀ x, inDomainInterval A B x -> (D x).Valid)
    (ha : inDomainInterval A B a) (hb : inDomainInterval A B b) (hab : a <= b)
    (m : Nat) (hm : 0 < m) : (leftSum D a b m).Valid := by
  apply Integral.finiteRawSum_valid
  intro X hX
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
  have him : i < m := List.mem_range.mp hi
  exact RealRaw.scaleRat_valid (hD _ (grid_mem ha hb hab hm (Nat.le_of_lt him)))

theorem sum_zero_function (m : Nat) : sum (fun _ => (0 : Rat)) m = 0 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [sum_succ, ih, Rat.add_zero]

end FiniteRiemannAlgebra
end ComputableAnalysis
