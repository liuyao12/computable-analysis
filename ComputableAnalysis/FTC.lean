import ComputableAnalysis.Differential
import ComputableAnalysis.Basic

/-!
# Effective fundamental theorem of calculus

This file contains the project-facing FTC theorem shape.  The concrete
calculus examples have deliberately been removed: the point here is the
general bridge from an `EffectiveFTC` certificate to equality of computable
real algorithms.
-/

namespace ComputableAnalysis

namespace FTC

theorem one_div_den_succ_le_of_pos {q : Rat} (hq : 0 < q) :
    1 / (((q.den + 1 : Nat) : Rat)) <= q := by
  let d : Rat := ((q.den + 1 : Nat) : Rat)
  have hdpos : 0 < d := by
    dsimp [d]
    exact (Rat.natCast_pos).2 (Nat.succ_pos q.den)
  have hnumpos : 0 < q.num := rat_num_pos_of_pos hq
  have hnumgeInt : (1 : Int) <= q.num := by omega
  have hnumge : (1 : Rat) <= (q.num : Rat) := by
    exact_mod_cast hnumgeInt
  have hqd :
      q * d = (q.num : Rat) + q := by
    dsimp [d]
    have hden := rat_den_mul_self q
    grind [Rat.mul_add, Rat.mul_assoc, Rat.mul_comm]
  have hqd_ge_one : 1 <= q * d := by
    rw [hqd]
    grind [Rat.le_of_lt hq]
  apply Rat.le_of_mul_le_mul_right (c := d)
  · calc
      (1 / d) * d = 1 := by
        rw [Rat.div_def]
        have hdne : d ≠ 0 := Rat.ne_of_gt hdpos
        grind [Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= q * d := hqd_ge_one
  · exact hdpos

theorem one_div_nat_antitone {n m : Nat}
    (hn : 0 < n) (hm : 0 < m) (hnm : n <= m) :
    (1 / (m : Rat)) <= 1 / (n : Rat) := by
  apply Rat.le_of_mul_le_mul_right (c := (n : Rat) * (m : Rat))
  · calc
      (1 / (m : Rat)) * ((n : Rat) * (m : Rat)) = (n : Rat) := by
        have hmne : (m : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hm)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
      _ <= (m : Rat) := by
        exact_mod_cast hnm
      _ = (1 / (n : Rat)) * ((n : Rat) * (m : Rat)) := by
        have hnne : (n : Rat) ≠ 0 :=
          Rat.ne_of_gt ((Rat.natCast_pos).2 hn)
        grind [Rat.div_def, Rat.mul_assoc, Rat.mul_comm, Rat.mul_inv_cancel]
  · exact Rat.mul_pos ((Rat.natCast_pos).2 hn) ((Rat.natCast_pos).2 hm)

def requestedPrecision (n : Nat) : QPos :=
  if hn : n = 0 then
    { val := 1, property := by native_decide }
  else
    { val := (1 / (n : Rat)), property := one_div_nat_pos (Nat.pos_of_ne_zero hn) }

def riemannComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    riemannLeftInterval dF a b
      (h.chooseN eps)
      (h.chooseEvalPrecision eps)

def endpointComputeOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : Nat -> QInterval :=
  fun n =>
    let eps := requestedPrecision n
    endpointDifferenceInterval F a b (h.chooseEvalPrecision eps)

def riemannRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealRaw where
  compute := riemannComputeOfEffectiveFTC h

def endpointRawOfEffectiveFTC
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) : RealRaw where
  compute := endpointComputeOfEffectiveFTC h

/-- General effective FTC, in computable-real form.

An `EffectiveFTC` certificate already says that, for every rational precision,
some finite Riemann sum for `dF` is close to the endpoint difference
`F(b)-F(a)`.  This theorem packages that certificate as equivalence of two
raw real algorithms: the scheduled Riemann sums and the scheduled endpoint
differences overlap at every requested stage. -/
theorem effectiveFTC_equiv_endpoint
    {F dF : RealFunRaw} {a b : Rat}
    (h : EffectiveFTC F dF a b) :
    (riemannRawOfEffectiveFTC h).Equiv (endpointRawOfEffectiveFTC h) := by
  apply RealRaw.sameStageOverlap_equiv
  intro n
  have hgood := h.good (requestedPrecision n)
  exact (RealRaw.compareAt_overlap_iff
    (riemannRawOfEffectiveFTC h) (endpointRawOfEffectiveFTC h) n n).2 hgood.1

end FTC

end ComputableAnalysis
