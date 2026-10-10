import ComputableAnalysis.RationalArchimedesModulus
import ComputableAnalysis.FiniteBallShellRecurrence

/-! Exact represented-real consequence of the finite Archimedes comparison.
The finite geometric comparison is an explicit hypothesis, not an equality
axiom and not yet proved for the sphere's incremental hull computation. -/
namespace ComputableAnalysis
namespace RealRaw

/-- Arbitrarily small endpoint separation implies exact equivalence. Only
nesting is used to transport the late comparisons to any earlier stage. -/
theorem equiv_of_endpoint_error {x y : RealRaw}
    (hx : x.Valid) (hy : y.Valid) (error : Nat → Rat)
    (herror : ShrinksToZero error)
    (hcompare : ∀ s,
      (x.compute s).lo ≤ (y.compute s).hi + error s ∧
      (y.compute s).lo ≤ (x.compute s).hi + error s) :
    x.Equiv y := by
  have direction : ∀ (a b : RealRaw), a.Valid → b.Valid →
      (∀ s, (a.compute s).lo ≤ (b.compute s).hi + error s) → a.Le b := by
    intro a b ha hb hab n m
    by_cases h : (a.compute n).lo ≤ (b.compute m).hi
    · exact h
    apply False.elim
    have hgap : 0 < (a.compute n).lo - (b.compute m).hi := by grind
    let eps : QPos := ⟨((a.compute n).lo - (b.compute m).hi)/2,
      by simpa [Rat.div_def] using Rat.mul_pos hgap (Rat.inv_pos.mpr (by decide : (0:Rat) < 2))⟩
    obtain ⟨N,hN⟩ := herror eps
    let s := max N (max n m)
    have hn : n ≤ s := Nat.le_trans (Nat.le_max_left n m) (Nat.le_max_right N _)
    have hm : m ≤ s := Nat.le_trans (Nat.le_max_right n m) (Nat.le_max_right N _)
    have he := hN s (Nat.le_max_left N _)
    have han := (ha.2.1 n s hn).1
    have hbm := (hb.2.1 m s hm).2.2
    have hc := hab s
    change error s ≤ ((a.compute n).lo - (b.compute m).hi)/2 at he
    grind
  exact equiv_of_le_of_ge
    (direction x y hx hy (fun s => (hcompare s).1))
    (direction y x hy hx (fun s => (hcompare s).2))

end RealRaw
namespace RationalBall

/-- The rational finite shell coefficient at stage s, with s+1 equal cells. -/
def archimedesPoints (s : Nat) : List Rat :=
  0 :: equalPartition 0 (1/((s+1:Nat):Rat)) (s+1)

def archimedesFactor (n : Nat) : Rat := 2/((n+2:Nat):Rat)

private theorem factor_nonneg (n : Nat) : 0 ≤ archimedesFactor n := by
  unfold archimedesFactor
  exact Rat.le_of_lt (Rat.mul_pos (by decide) (Rat.inv_pos.mpr
    (Rat.natCast_pos.mpr (by omega))))

/-- Exact Archimedes step for a supplied valid product computation and a
supplied next-dimensional computation satisfying the finite shell comparison.
No equality, recurrence, integral, or curved-region volume is assumed. -/
theorem archimedes_step_of_shell_comparison
    (n : Nat) (hn : 0 < n) (next product : RealRaw)
    (hnext : next.Valid) (hproduct : product.Valid)
    (B : Rat) (hB : 0 < B)
    (hbounds : ∀ s, 0 ≤ (product.compute s).lo ∧ (product.compute s).hi ≤ B)
    (hgeometry : ∀ s,
      (next.compute s).lo ≤ shellUpper n (archimedesPoints s) * (product.compute s).hi ∧
      shellLower n (archimedesPoints s) * (product.compute s).lo ≤ (next.compute s).hi) :
    next.Equiv (RealRaw.scaleRat (archimedesFactor n) product) := by
  have hy := RealRaw.scaleRat_valid_of_nonneg (factor_nonneg n) hproduct
  apply RealRaw.equiv_of_endpoint_error hnext hy
    (fun s => 3*B/((s+1:Nat):Rat))
    (RationalArchimedesModulus.shrinksToZero_of_ratOverSuccBound (fun _ => Rat.le_refl))
  intro s
  have hs := uniform_shells_recurrence_estimate n (s+1) hn (by omega)
  change archimedesFactor n - 2/((s+1:Nat):Rat) ≤ shellLower n (archimedesPoints s) ∧
    shellLower n (archimedesPoints s) ≤ archimedesFactor n + 1/((s+1:Nat):Rat) ∧
    shellLower n (archimedesPoints s) ≤ shellUpper n (archimedesPoints s) ∧
    shellUpper n (archimedesPoints s) ≤ archimedesFactor n + 3/((s+1:Nat):Rat) at hs
  have hp := hbounds s
  have ho := RealRaw.interval_order_of_valid product hproduct s
  have hhi : 0 ≤ (product.compute s).hi := Rat.le_trans hp.1 ho
  have hloB : (product.compute s).lo ≤ B := Rat.le_trans ho hp.2
  have hd : 0 ≤ (1:Rat)/((s+1:Nat):Rat) := by
    simpa [Rat.div_def] using Rat.le_of_lt
      (Rat.inv_pos.mpr (Rat.natCast_pos.mpr (by omega : 0 < s+1)))
  have herror23 : 2/((s+1:Nat):Rat)*B ≤ 3*B/((s+1:Nat):Rat) := by
    have ht := Rat.mul_nonneg (Rat.le_of_lt hB) hd
    grind [Rat.div_def,Rat.mul_assoc,Rat.mul_comm]
  have hu := Rat.mul_le_mul_of_nonneg_right hs.2.2.2 hhi
  have hl := Rat.mul_le_mul_of_nonneg_right hs.1 hp.1
  have huB := Rat.mul_le_mul_of_nonneg_left hp.2 (by grind : 0 ≤ 3/((s+1:Nat):Rat))
  have hlB := Rat.mul_le_mul_of_nonneg_left hloB (by grind : 0 ≤ 2/((s+1:Nat):Rat))
  have hg := hgeometry s
  unfold RealRaw.scaleRat RealRaw.scaleRatCompute
  simp only [factor_nonneg n, if_true]
  constructor <;> grind [Rat.div_def, Rat.add_mul, Rat.sub_eq_add_neg, Rat.mul_assoc, Rat.mul_comm]

/-- The public dimension-step conclusion is exact raw-real equivalence.
The remaining geometric obligation is the finite shell comparison `hgeometry`
for the actual incremental ball computations; this theorem does not discharge
that obligation by defining volumes recursively. -/
theorem ball_recurrence_of_shell_comparison
    (n : Nat) (hn : 0 < n) (disk vn vn2 : RealRaw)
    (hdisk : disk.Valid) (hvn : vn.Valid) (hvn2 : vn2.Valid)
    (D V : Rat) (hD : 0 < D) (hV : 0 < V)
    (hdiskBounds : ∀ s, 0 ≤ (disk.compute s).lo ∧ (disk.compute s).hi ≤ D)
    (hvnBounds : ∀ s, 0 ≤ (vn.compute s).lo ∧ (vn.compute s).hi ≤ V)
    (hgeometry : ∀ s,
      (vn2.compute s).lo ≤ shellUpper n (archimedesPoints s) * ((disk*vn).compute s).hi ∧
      shellLower n (archimedesPoints s) * ((disk*vn).compute s).lo ≤ (vn2.compute s).hi) :
    vn2.Equiv (RealRaw.scaleRat (2/((n+2:Nat):Rat)) (disk*vn)) := by
  have hp := RealRaw.mul_valid_of_nonneg_bounded hdisk hvn hD hV hdiskBounds hvnBounds
  have hb : ∀ s, 0 ≤ ((disk*vn).compute s).lo ∧ ((disk*vn).compute s).hi ≤ D*V := by
    intro s
    have hd := hdiskBounds s
    have hv := hvnBounds s
    have hod := RealRaw.interval_order_of_valid disk hdisk s
    have hov := RealRaw.interval_order_of_valid vn hvn s
    have he : (disk*vn).compute s =
        {lo := (disk.compute s).lo*(vn.compute s).lo,
         hi := (disk.compute s).hi*(vn.compute s).hi} := by
      change QBox.mulRealInterval _ _ _ _ = _
      exact QBox.mulRealInterval_of_nonneg hd.1 hod hv.1 hov
    rw [he]
    constructor
    · exact Rat.mul_nonneg hd.1 hv.1
    · have h1 := Rat.mul_le_mul_of_nonneg_right hd.2 (Rat.le_trans hv.1 hov)
      have h2 := Rat.mul_le_mul_of_nonneg_left hv.2 (Rat.le_of_lt hD)
      exact Rat.le_trans h1 h2
  exact archimedes_step_of_shell_comparison n hn vn2 (disk*vn)
    hvn2 hp (D*V) (Rat.mul_pos hD hV) hb hgeometry

#print axioms RealRaw.equiv_of_endpoint_error
#print axioms archimedes_step_of_shell_comparison
#print axioms ball_recurrence_of_shell_comparison
end RationalBall
end ComputableAnalysis
