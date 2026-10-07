import ComputableAnalysis.ModularForms.Hecke41WordInvariance

namespace ComputableAnalysis.ModularForms

def SL2Z.translation (n : Int) : SL2Z := ⟨1,n,0,1,by simp⟩

def ModularWord.powerWord (g : ModularWord) : Nat → ModularWord
  | 0 => .identity
  | n+1 => .multiply g (powerWord g n)

private theorem repeat_T (n : Nat) : (ModularWord.powerWord .T n).matrix = SL2Z.translation n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change SL2Z.multiply SL2Z.T _ = _
      rw [ih]
      apply SL2Z.ext <;> simp [SL2Z.multiply,SL2Z.translation,SL2Z.T] <;> omega

private theorem repeat_inverseT (n : Nat) :
    (ModularWord.powerWord ModularWord.inverseT n).matrix = SL2Z.translation (- (n : Int)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change SL2Z.multiply ModularWord.inverseT.matrix _ = _
      rw [ModularWord.inverseT_matrix, ih]
      apply SL2Z.ext <;> simp [SL2Z.multiply,SL2Z.translation,SL2Z.T,SL2Z.inverse] <;> omega

/-- Executable word for translation by any signed integer. -/
def ModularWord.translation (n : Int) : ModularWord :=
  if 0 ≤ n then powerWord .T n.natAbs else powerWord inverseT n.natAbs

theorem ModularWord.translation_matrix (n : Int) : (translation n).matrix = SL2Z.translation n := by
  unfold translation
  split
  · rw [repeat_T, Int.natAbs_of_nonneg (by assumption)]
  · rw [repeat_inverseT]
    congr 1
    have hn : 0 ≤ -n := by omega
    have h := Int.natAbs_of_nonneg hn
    rw [Int.natAbs_neg] at h
    omega

/-- Euclidean reduction constructs a finite S,T word for every modular matrix. -/
theorem SL2Z.exists_modularWord (g : SL2Z) : ∃ w : ModularWord, w.matrix = g := by
  by_cases hc : g.c = 0
  · have had : g.a*g.d = 1 := by have h := g.determinant; simpa [hc] using h
    by_cases ha : 0 ≤ g.a
    · have ha1 := Int.eq_one_of_mul_eq_one_right ha had
      have hd1 : g.d = 1 := by rw [ha1] at had; simpa using had
      refine ⟨ModularWord.translation g.b, ?_⟩
      rw [ModularWord.translation_matrix]
      apply SL2Z.ext <;> simp [SL2Z.translation,ha1,hd1,hc]
    · have hn : (-g.a)*(-g.d)=1 := by grind
      have ha1 := Int.eq_one_of_mul_eq_one_right (show 0 ≤ -g.a by omega) hn
      have ha' : g.a = -1 := by omega
      have hd' : g.d = -1 := by rw [ha'] at had; omega
      refine ⟨.multiply (.multiply .S .S) (ModularWord.translation (-g.b)), ?_⟩
      change SL2Z.multiply (SL2Z.multiply SL2Z.S SL2Z.S) _ = _
      rw [SL2Z.S_square, ModularWord.translation_matrix]
      apply SL2Z.ext <;> simp [SL2Z.multiply,SL2Z.minusIdentity,SL2Z.translation,ha',hd',hc]
  · let q := g.a / g.c
    let h := SL2Z.multiply SL2Z.S (SL2Z.multiply (SL2Z.translation (-q)) g)
    have hh : h.c = g.a % g.c := by
      have he := Int.mul_ediv_add_emod g.a g.c
      dsimp [h,SL2Z.multiply,SL2Z.S,SL2Z.translation,q]
      grind
    have hsmall : h.c.natAbs < g.c.natAbs := by
      rw [hh]
      have hl := Int.natAbs_lt_natAbs_of_nonneg_of_lt (Int.emod_nonneg g.a hc) (Int.emod_lt g.a hc)
      simpa using hl
    obtain ⟨w, hw⟩ := SL2Z.exists_modularWord h
    refine ⟨.multiply (ModularWord.translation q) (.multiply ModularWord.inverseS w), ?_⟩
    change SL2Z.multiply (ModularWord.translation q).matrix (SL2Z.multiply ModularWord.inverseS.matrix w.matrix) = _
    rw [ModularWord.translation_matrix, ModularWord.inverseS_matrix, hw]
    apply SL2Z.ext <;> simp [h, SL2Z.multiply,SL2Z.S,SL2Z.inverse,SL2Z.translation] <;> grind
termination_by g.c.natAbs

end ComputableAnalysis.ModularForms
