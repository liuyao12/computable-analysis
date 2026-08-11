import ComputableAnalysis.FiniteDyadicAMGM

/-!
# A worked finite dyadic AM--GM certificate

The four leaves `1,2,3,4` form a depth-two binary certificate.  The example
checks its finite sum/product data and invokes the generic dyadic AM--GM
bound; no infinite averaging process is involved.
-/

namespace ComputableAnalysis

open DyadicAMGM

def dyadicAMGMExample : DyadicAMGM 2 :=
  .branch
    (.branch (.leaf 1 (by native_decide)) (.leaf 2 (by native_decide)))
    (.branch (.leaf 3 (by native_decide)) (.leaf 4 (by native_decide)))

theorem dyadicAMGMExample_sum :
    DyadicAMGM.sum dyadicAMGMExample = 10 := by
  native_decide

theorem dyadicAMGMExample_product :
    DyadicAMGM.product dyadicAMGMExample = 24 := by
  native_decide

theorem dyadicAMGMExample_certificate :
    DyadicAMGM.product dyadicAMGMExample ≤
      (DyadicAMGM.sum dyadicAMGMExample / ((2 ^ 2 : Nat) : Rat)) ^ (2 ^ 2) := by
  exact DyadicAMGM.product_le_average_pow dyadicAMGMExample

theorem dyadicAMGMExample_numeric_bound :
    (24 : Rat) ≤ (10 / 4) ^ 4 := by
  native_decide

def dyadicAMGMExampleDepthThree : DyadicAMGM 3 :=
  .branch
    (.branch
      (.branch (.leaf 1 (by native_decide)) (.leaf 2 (by native_decide)))
      (.branch (.leaf 3 (by native_decide)) (.leaf 4 (by native_decide))))
    (.branch
      (.branch (.leaf 5 (by native_decide)) (.leaf 6 (by native_decide)))
      (.branch (.leaf 7 (by native_decide)) (.leaf 8 (by native_decide))))

theorem dyadicAMGMExampleDepthThree_sum :
    DyadicAMGM.sum dyadicAMGMExampleDepthThree = 36 := by
  native_decide

theorem dyadicAMGMExampleDepthThree_product :
    DyadicAMGM.product dyadicAMGMExampleDepthThree = 40320 := by
  native_decide

theorem dyadicAMGMExampleDepthThree_certificate :
    DyadicAMGM.product dyadicAMGMExampleDepthThree ≤
      (DyadicAMGM.sum dyadicAMGMExampleDepthThree /
        ((2 ^ 3 : Nat) : Rat)) ^ (2 ^ 3) := by
  exact DyadicAMGM.product_le_average_pow dyadicAMGMExampleDepthThree

theorem dyadicAMGMExampleDepthThree_numeric_bound :
    (40320 : Rat) ≤ (36 / 8) ^ 8 := by
  native_decide

def dyadicAMGMExampleDepthFour : DyadicAMGM 4 :=
  .branch
    (.branch
      (.branch
        (.branch (.leaf 1 (by native_decide)) (.leaf 2 (by native_decide)))
        (.branch (.leaf 3 (by native_decide)) (.leaf 4 (by native_decide))))
      (.branch
        (.branch (.leaf 5 (by native_decide)) (.leaf 6 (by native_decide)))
        (.branch (.leaf 7 (by native_decide)) (.leaf 8 (by native_decide)))))
    (.branch
      (.branch
        (.branch (.leaf 9 (by native_decide)) (.leaf 10 (by native_decide)))
        (.branch (.leaf 11 (by native_decide)) (.leaf 12 (by native_decide))))
      (.branch
        (.branch (.leaf 13 (by native_decide)) (.leaf 14 (by native_decide)))
        (.branch (.leaf 15 (by native_decide)) (.leaf 16 (by native_decide)))))

theorem dyadicAMGMExampleDepthFour_sum :
    DyadicAMGM.sum dyadicAMGMExampleDepthFour = 136 := by
  native_decide

theorem dyadicAMGMExampleDepthFour_product :
    DyadicAMGM.product dyadicAMGMExampleDepthFour = 20922789888000 := by
  native_decide

theorem dyadicAMGMExampleDepthFour_certificate :
    DyadicAMGM.product dyadicAMGMExampleDepthFour ≤
      (DyadicAMGM.sum dyadicAMGMExampleDepthFour /
        ((2 ^ 4 : Nat) : Rat)) ^ (2 ^ 4) := by
  exact DyadicAMGM.product_le_average_pow dyadicAMGMExampleDepthFour

theorem dyadicAMGMExampleDepthFour_numeric_bound :
    (20922789888000 : Rat) ≤ (136 / 16) ^ 16 := by
  native_decide

def consecutiveDyadic (start : Nat) : (depth : Nat) → DyadicAMGM depth
  | 0 =>
      .leaf (start : Rat) (by
        exact_mod_cast Nat.zero_le start)
  | depth + 1 =>
      .branch (consecutiveDyadic start depth)
        (consecutiveDyadic (start + 2 ^ depth) depth)

def dyadicAMGMExampleDepthFive : DyadicAMGM 5 :=
  consecutiveDyadic 1 5

theorem dyadicAMGMExampleDepthFive_sum :
    DyadicAMGM.sum dyadicAMGMExampleDepthFive = 528 := by
  native_decide

theorem dyadicAMGMExampleDepthFive_product :
    DyadicAMGM.product dyadicAMGMExampleDepthFive =
      263130836933693530167218012160000000 := by
  native_decide

theorem dyadicAMGMExampleDepthFive_certificate :
    DyadicAMGM.product dyadicAMGMExampleDepthFive ≤
      (DyadicAMGM.sum dyadicAMGMExampleDepthFive /
        ((2 ^ 5 : Nat) : Rat)) ^ (2 ^ 5) := by
  exact DyadicAMGM.product_le_average_pow dyadicAMGMExampleDepthFive

theorem dyadicAMGMExampleDepthFive_numeric_bound :
    (263130836933693530167218012160000000 : Rat) ≤ (528 / 32) ^ 32 := by
  native_decide

end ComputableAnalysis
