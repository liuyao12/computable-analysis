import ComputableAnalysis.ModularForms.UpperRegionalWeightFourTails
import ComputableAnalysis.ModularForms.UpperRegionalWeightSixTails
import ComputableAnalysis.ModularForms.UpperWeightFourSum
import ComputableAnalysis.ModularForms.UpperWeightSixSum

/-! Regional bounds on actual infinite-sum prefix remainders. -/
namespace ComputableAnalysis.ModularForms
open RiemannHilbert FunctionTheory ComplexRaw

private theorem triangle (F q p : ComplexRaw) (hF : F.Valid) (hq : q.Valid) (hp : p.Valid)
    (a b : Rat) (h1 : Small (sub F q) a) (h2 : Small (sub q p) b) :
    Small (sub F p) (a+b) := by
  have he : (add (sub F q) (sub q p)).Equiv (sub F p) := by
    apply ComplexRawQuotient.equiv_of_ofRaw_eq
      (hleft := add_valid (sub_valid hF hq) (sub_valid hq hp)) (hright := sub_valid hF hp)
    change (ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw q hq)+
      (ComplexRawQuotient.ofRaw q hq-ComplexRawQuotient.ofRaw p hp)=
      ComplexRawQuotient.ofRaw F hF-ComplexRawQuotient.ofRaw p hp
    grind only
  exact Small.congr (add_valid (sub_valid hF hq) (sub_valid hq hp))
    (sub_valid hF hp) he (LocalODE.small_add h1 h2)

theorem upperWeightFourLatticeSum_region_close_prefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (n : Nat) :
    Small (sub (upperWeightFourLatticeSum z hz) (upperWeightFourPrefix z hz n))
      (regionalWeightFourTailConstant R H eta*reciprocalSquare (n+1)) := by
  apply SeriesLimitLaws.small_closed _ _ (fun k => upperWeightFourTailRate z hz (k+n))
    (SeriesLimitLaws.shrinks_shift _ (upperWeightFourTailRate_shrinks z hz) n)
  intro k
  have he : (n+1)+k=n+k+1 := by omega
  have hd := upperWeightFourPrefix_difference z hz (n+1) k
  rw [he] at hd
  have hb := Small.congr (upperWeightFourTailBlock_valid z hz (n+1) k)
    (sub_valid (upperWeightFourPrefix_valid z hz (n+k)) (upperWeightFourPrefix_valid z hz n))
    (equiv_symm hd)
    (regionalWeightFourTailBlock_uniform_small z hz R H eta S hR hH heta hregion hheight
      (n+1) k (by omega))
  have ht := triangle _ _ _ (upperWeightFourLatticeSum_valid z hz)
    (upperWeightFourPrefix_valid z hz (n+k)) (upperWeightFourPrefix_valid z hz n) _ _
    (upperWeightFourLatticeSum_close_prefix z hz (n+k)) hb
  simpa only [Nat.add_comm,Rat.add_comm] using ht

theorem upperWeightSixLatticeSum_region_close_prefix (z : Scalar) (hz : InUpperHalfPlane z.val)
    (R H eta : Rat) (S : Nat) (hR : 0≤R) (hH : 0≤H) (heta : 0<eta)
    (hregion : LatticeRegionBox z R eta S) (hheight : (z.val.compute S).hi.im≤H) (n : Nat) :
    Small (sub (upperWeightSixLatticeSum z hz) (upperWeightSixPrefix z hz n))
      (regionalWeightSixTailConstant R H eta*reciprocalSquare (n+1)) := by
  apply SeriesLimitLaws.small_closed _ _ (fun k => upperWeightSixTailRate z hz (k+n))
    (SeriesLimitLaws.shrinks_shift _ (upperWeightSixTailRate_shrinks z hz) n)
  intro k
  have he : (n+1)+k=n+k+1 := by omega
  have hd := upperWeightSixPrefix_difference z hz (n+1) k
  rw [he] at hd
  have hb := Small.congr (upperWeightSixTailBlock_valid z hz (n+1) k)
    (sub_valid (upperWeightSixPrefix_valid z hz (n+k)) (upperWeightSixPrefix_valid z hz n))
    (equiv_symm hd)
    (regionalWeightSixTailBlock_uniform_small z hz R H eta S hR hH heta hregion hheight
      (n+1) k (by omega))
  have ht := triangle _ _ _ (upperWeightSixLatticeSum_valid z hz)
    (upperWeightSixPrefix_valid z hz (n+k)) (upperWeightSixPrefix_valid z hz n) _ _
    (upperWeightSixLatticeSum_close_prefix z hz (n+k)) hb
  simpa only [Nat.add_comm,Rat.add_comm] using ht

end ComputableAnalysis.ModularForms
