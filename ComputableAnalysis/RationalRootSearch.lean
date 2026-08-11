import ComputableAnalysis.Polynomial

namespace ComputableAnalysis

/-! A finite rational candidate search for polynomial roots.

The search is deliberately conditional on the supplied candidate list.  It
does not claim that the list contains a root, nor that an arbitrary
polynomial has a rational root. -/
namespace RationalRootSearch

def rationalRootSearch (coeffs : List Rat) : List Rat -> Option Rat
  | [] => none
  | r :: candidates =>
      if Polynomial.eval coeffs r = 0 then
        some r
      else
        rationalRootSearch coeffs candidates

theorem rationalRootSearch_sound
    {coeffs : List Rat} {candidates : List Rat} {r : Rat}
    (hsearch : rationalRootSearch coeffs candidates = some r) :
    Polynomial.eval coeffs r = 0 := by
  induction candidates with
  | nil => simp [rationalRootSearch] at hsearch
  | cons candidate candidates ih =>
      by_cases hroot : Polynomial.eval coeffs candidate = 0
      · simp [rationalRootSearch, hroot] at hsearch
        cases hsearch
        exact hroot
      · simp [rationalRootSearch, hroot] at hsearch
        exact ih hsearch

theorem rationalRootSearch_complete
    {coeffs : List Rat} {candidates : List Rat}
    (hroot : ∃ r ∈ candidates, Polynomial.eval coeffs r = 0) :
    ∃ r, rationalRootSearch coeffs candidates = some r ∧
      Polynomial.eval coeffs r = 0 := by
  induction candidates with
  | nil => simp at hroot
  | cons candidate candidates ih =>
      rcases hroot with ⟨r, hr, hvalue⟩
      simp only [List.mem_cons] at hr
      by_cases hcandidate : Polynomial.eval coeffs candidate = 0
      · exact ⟨candidate, by simp [rationalRootSearch, hcandidate], hcandidate⟩
      · rcases hr with rfl | hr
        · exact False.elim (hcandidate hvalue)
        · have htail : ∃ r ∈ candidates, Polynomial.eval coeffs r = 0 :=
            ⟨r, hr, hvalue⟩
          rcases ih htail with ⟨r', hsearch, hroot'⟩
          exact ⟨r', by simp [rationalRootSearch, hcandidate, hsearch], hroot'⟩

theorem rationalRootSearch_complete_of_mem
    {coeffs : List Rat} {candidates : List Rat} {r : Rat}
    (hr : r ∈ candidates) (hroot : Polynomial.eval coeffs r = 0) :
    ∃ r', rationalRootSearch coeffs candidates = some r' ∧
      Polynomial.eval coeffs r' = 0 :=
  rationalRootSearch_complete ⟨r, hr, hroot⟩

theorem rationalRootSearch_none_iff
    {coeffs : List Rat} {candidates : List Rat} :
    rationalRootSearch coeffs candidates = none ↔
      ∀ r ∈ candidates, Polynomial.eval coeffs r ≠ 0 := by
  constructor
  · intro hnone r hr hroot
    rcases rationalRootSearch_complete ⟨r, hr, hroot⟩ with
      ⟨r', hsearch, _⟩
    rw [hnone] at hsearch
    cases hsearch
  · intro hall
    induction candidates with
    | nil => rfl
    | cons candidate candidates ih =>
        by_cases hcandidate : Polynomial.eval coeffs candidate = 0
        · exact False.elim (hall candidate (by simp) hcandidate)
        · simp only [rationalRootSearch, hcandidate]
          apply ih
          intro r hr
          exact hall r (by simp [hr])

/-! The search result packaged with the project's finite synthetic-division
certificate.  The dependent sum records which rational candidate was found. -/

def rationalRootSearchCertificate (coeffs : List Rat) (candidates : List Rat) :
    Option (Σ r : Rat, Polynomial.RemainderCertificate coeffs r) :=
  match rationalRootSearch coeffs candidates with
  | none => none
  | some r => some ⟨r, Polynomial.syntheticRemainderCertificate r coeffs⟩

theorem rationalRootSearchCertificate_sound
    {coeffs : List Rat} {candidates : List Rat}
    {certificate : Σ r : Rat, Polynomial.RemainderCertificate coeffs r}
    (hcertificate : rationalRootSearchCertificate coeffs candidates = some certificate) :
    Polynomial.eval coeffs certificate.1 = 0 := by
  cases hsearch : rationalRootSearch coeffs candidates with
  | none =>
      simp [rationalRootSearchCertificate, hsearch] at hcertificate
  | some r =>
      simp [rationalRootSearchCertificate, hsearch] at hcertificate
      cases hcertificate
      exact rationalRootSearch_sound hsearch

theorem rationalRootSearchCertificate_complete
    {coeffs : List Rat} {candidates : List Rat}
    (hroot : ∃ r ∈ candidates, Polynomial.eval coeffs r = 0) :
    ∃ certificate,
      rationalRootSearchCertificate coeffs candidates = some certificate ∧
        Polynomial.eval coeffs certificate.1 = 0 := by
  rcases rationalRootSearch_complete hroot with ⟨r, hsearch, hvalue⟩
  refine ⟨⟨r, Polynomial.syntheticRemainderCertificate r coeffs⟩, ?_, ?_⟩
  · simp [rationalRootSearchCertificate, hsearch]
  · exact hvalue

end RationalRootSearch

end ComputableAnalysis
