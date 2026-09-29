import ComputableAnalysis.IntegralRectangleSpecification

/-! Conditional exhaustion laws. Concrete integrands must separately supply
compact integral evidence, domain coverage, and an effective tail estimate. -/
namespace ComputableAnalysis
namespace Integral

/-- Exact closeness expressed through all rational approximations. -/
def Within (I J : RealRaw) (eps : Rat) : Prop :=
  ∀ n m, (I.compute n).lo ≤ (J.compute m).hi + eps ∧
    (J.compute m).lo ≤ (I.compute n).hi + eps

/-- A limit of actual compact integrals along a supplied exhaustion.
The compact-witness field prevents a vacuous convergence condition when none
of the finite integrals have been constructed. Domain coverage and any
substitution identifying an improper integral belong to the exhaustion proof. -/
structure HasIntegralLimit (F : Nat → FunctionOnInterval) (I : RealRaw) : Prop where
  valid : I.Valid
  compact : ∀ n, ∃ J, HasIntegral (F n) J
  converges : ∀ eps : QPos, ∃ N, ∀ n, N ≤ n →
    ∀ J, HasIntegral (F n) J → Within I J eps.val

theorem HasIntegralLimit.unique {F : Nat → FunctionOnInterval} {I J : RealRaw}
    (hI : HasIntegralLimit F I) (hJ : HasIntegralLimit F J) : I.Equiv J := by
  have hle : ∀ (X Y : RealRaw), HasIntegralLimit F X →
      HasIntegralLimit F Y → X.Le Y := by
    intro X Y hX hY n m
    by_cases h : (X.compute n).lo ≤ (Y.compute m).hi
    · exact h
    exfalso
    let gap := (X.compute n).lo - (Y.compute m).hi
    have hg : 0 < gap / 4 := by dsimp [gap]; grind
    let eps : QPos := ⟨gap/4, hg⟩
    obtain ⟨Nx, hx⟩ := hX.converges eps
    obtain ⟨Ny, hy⟩ := hY.converges eps
    obtain ⟨K, hK⟩ := hX.compact (max Nx Ny)
    obtain ⟨s, hs⟩ := hK.valid.2.2 eps
    have hw := hs s (Nat.le_refl _)
    have hxk := (hx (max Nx Ny) (Nat.le_max_left _ _) K hK n s).1
    have hyk := (hy (max Nx Ny) (Nat.le_max_right _ _) K hK m s).2
    change (K.compute s).width ≤ gap/4 at hw
    change (X.compute n).lo ≤ (K.compute s).hi + gap/4 at hxk
    change (K.compute s).lo ≤ (Y.compute m).hi + gap/4 at hyk
    dsimp [gap] at hw hxk hyk
    grind [QInterval.width]
  exact RealRaw.equiv_of_le_of_ge (hle I J hI hJ) (hle J I hJ hI)

theorem rational_upper_natural (q : Rat) :
    q <= (((q.num.natAbs : Nat) : Rat) + 1) := by
  by_cases hqpos : 0 < q
  · have hdenpos : 0 < ((q.den : Nat) : Rat) := by
      exact (Rat.natCast_pos).2 (Nat.pos_of_ne_zero q.den_nz)
    apply Rat.le_of_mul_le_mul_right (c := ((q.den : Nat) : Rat))
    · rw [Rat.mul_comm q ((q.den : Nat) : Rat), rat_den_mul_self]
      have hnumpos : 0 < q.num := rat_num_pos_of_pos hqpos
      have hnum_nonneg : 0 <= q.num := Int.le_of_lt hnumpos
      have hcast : (((q.num.natAbs : Nat) : Rat)) = (q.num : Rat) := by
        exact_mod_cast (Int.natAbs_of_nonneg hnum_nonneg)
      calc
        (q.num : Rat) = ((q.num.natAbs : Nat) : Rat) := by rw [hcast]
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) := by
          exact_mod_cast (Nat.le_succ q.num.natAbs)
        _ <= (((q.num.natAbs : Nat) : Rat) + 1) *
            ((q.den : Nat) : Rat) := by
          exact_mod_cast (Nat.le_mul_of_pos_right (q.num.natAbs + 1)
            (Nat.pos_of_ne_zero q.den_nz))
    · exact hdenpos
  · have hqnonpos : q <= 0 := by grind
    have hzero : (0 : Rat) <= (((q.num.natAbs : Nat) : Rat) + 1) := by
      exact_mod_cast (Nat.zero_le (q.num.natAbs + 1))
    exact Rat.le_trans hqnonpos hzero


/-- A proved finite lower bound growing with the exhaustion rules out every
valid represented limit. No infinite value or comparison axiom is postulated. -/
theorem no_limit_of_growing_lower_bounds {F : Nat → FunctionOnInterval}
    (hF : ∀ n J, HasIntegral (F n) J → (RealRaw.ofRat (n : Rat)).Le J)
    (I : RealRaw) : ¬ HasIntegralLimit F I := by
  intro hI
  let eps : QPos := ⟨1,by decide⟩
  obtain ⟨N,hN⟩ := hI.converges eps
  let C := (I.compute 0).hi+2
  let T := C.num.natAbs+2
  have hC := rational_upper_natural C
  have hT : C < (T : Rat) := by dsimp [T]; push_cast; grind only
  let n := max N T
  obtain ⟨J,hJ⟩ := hI.compact n
  obtain ⟨s,hs⟩ := hJ.valid.2.2 eps
  have hw := hs s (Nat.le_refl _)
  have hlow := hF n J hJ 0 s
  have hclose := (hN n (Nat.le_max_left _ _) J hJ 0 s).2
  have hlarge : (T : Rat) ≤ (n : Rat) := by exact_mod_cast (Nat.le_max_right N T)
  change (J.compute s).hi-(J.compute s).lo ≤ 1 at hw
  change (n : Rat) ≤ (J.compute s).hi at hlow
  change (J.compute s).lo ≤ (I.compute 0).hi+1 at hclose
  dsimp [C] at hT
  grind only

end Integral
end ComputableAnalysis
