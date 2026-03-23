import VectorCommitmentsLean.RSA
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Basic
@[grind]
structure FixedArray (q: ℕ) (α : Type) where
  arr : Array α
  proof : arr.size = q
@[grind]
structure PublicParameters  (q: ℕ) where 
  N : ℕ
  a : ℕ
  e_array : FixedArray q ℕ
  S_array : FixedArray q ℕ
  
@[grind]
structure UpdateInfo where
  m : ℕ
  m' : ℕ
  i : ℕ

abbrev Auxillary (q : ℕ) := FixedArray q ℕ
@[grind]
def KeyGen (p₁ p₂ q: ℕ) (a: ℕ) (e_array: FixedArray q ℕ) (_ : p₁ ≠ p₂)(_: p₁.Prime) (_: p₂.Prime) (_: ∀ e ∈ e_array.arr, e.Coprime (p₁ * p₂).totient ∧ 1 < e ∧ e < (p₁ * p₂).totient): PublicParameters q := 
  {
    N := p₁ * p₂,
    a := a,
    e_array := e_array,
    S_array := {arr := (Array.finRange q).map (fun i => a ^ ((Array.finRange q).map (fun j => if i == j then 1 else e_array.arr[j]!)).foldr (· * ·) 1), proof := by simp} 
  }
@[grind]
def Commitment {q: ℕ} (pp: PublicParameters q)(m_array: FixedArray q ℕ) : ℕ × Auxillary q := 
  (((Array.finRange q).map (fun i => pp.S_array.arr[i]! ^ m_array.arr[i]!)).foldr (· * ·) 1, m_array)
@[grind]
def Open {q: ℕ} (pp: PublicParameters q) (_: ℕ) (i: ℕ) (aux : Auxillary q) : ℕ :=
  ((pp.e_array.arr[i]!).floorRoot (((Array.finRange q).map (fun (k: Fin q) => if k.1 == i then 1 else pp.S_array.arr[k]! ^ aux.arr[k]!)).foldr (· * ·) 1))  % pp.N

@[grind]
def Verify {q: ℕ} (pp: PublicParameters q) (C m i proof : ℕ) : Bool :=
  if C == (pp.S_array.arr[i]! ^ m) * (proof ^ pp.e_array.arr[i]!) % pp.N then Bool.true else Bool.false

@[grind]
def Update {q: ℕ} (pp: PublicParameters q) (C m m' i: ℕ) : ℕ × UpdateInfo := 
  (C * pp.S_array.arr[i]!^(m' - m), {m := m, m' := m', i := i})
@[grind]
def ProofUpdate {q: ℕ} (pp: PublicParameters q) (C proof j m' i: ℕ) (U: UpdateInfo) : ℕ × ℕ :=
  if i != j then
    (C * pp.S_array.arr[i]!^(m' - U.m), proof * pp.e_array.arr[i]!.floorRoot (pp.S_array.arr[i]!^(m' - U.m)))
  else
    (C * pp.S_array.arr[i]!^(m' - U.m), proof)

theorem normal_correctness {q: ℕ} 
  (pp: PublicParameters q)
  (C: ℕ)
  (aux : Auxillary q)
  (m i: ℕ)
  (m_array: FixedArray q ℕ)
  (valid_index: i < m_array.arr.size)
  (proof: ℕ)
  (validPublicKey: ∃ p₁ p₂  a e_array neq hp₁ hp₂ he, KeyGen p₁ p₂ q a e_array neq hp₁ hp₂  he = pp)
  (validCommitment:  Commitment pp m_array = (C, aux))
  (validProof: Open pp m i aux = proof)
  (c_less: C < pp.N)
  :  m == m_array.arr[i]'valid_index → Verify pp C m i proof == Bool.true:= 
    by
      intro mCorrect 
      rcases validPublicKey with ⟨p₁, p₂, a, e_array, neq, hp₁, hp₂, he, validPublicKey⟩
      simp [Verify]
      simp [KeyGen] at validPublicKey
      simp [Commitment] at validCommitment
      simp [Open] at validProof
      cases validPublicKey
      simp at *
      -- rw [Array.getElem_map (sorry)]
      sorry
