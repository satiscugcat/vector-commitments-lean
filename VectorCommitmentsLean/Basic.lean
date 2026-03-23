import VectorCommitmentsLean.RSA
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Basic

structure FixedArray (q: ℕ) (α : Type) where
  arr : Array α
  proof : arr.size = q
structure PublicParameters  (q: ℕ) where 
  N : ℕ
  a : ℕ
  e_array : FixedArray q ℕ
  S_array : FixedArray q ℕ
  

structure UpdateInfo where
  m : ℕ
  m' : ℕ
  i : ℕ

abbrev Auxillary (q : ℕ) := FixedArray q ℕ

def KeyGen (p₁ p₂ q: ℕ) (a: ℕ) (e_array: FixedArray q ℕ) (_: p₁.Prime) (_: p₂.Prime) (_: ∀ e ∈ e_array.arr, e.Coprime (p * q).totient): PublicParameters q := 
  {
    N := p * q,
    a := a,
    e_array := e_array,
    S_array := {arr := (Array.finRange q).map (fun i => a ^ ((Array.finRange q).map (fun j => if i == j then 1 else e_array.arr[j]!)).foldr (· * ·) 1), proof := by simp} 
  }

def Commitment {q: ℕ} (pp: PublicParameters q)(m_array: FixedArray q ℕ) : ℕ × Auxillary q := 
  (((Array.finRange q).map (fun i => pp.S_array.arr[i]! ^ m_array.arr[i]!)).foldr (· * ·) 1, m_array)

def Open {q: ℕ} (pp: PublicParameters q) (_: ℕ) (i: ℕ) (aux : Auxillary q) : ℕ :=
  ((pp.e_array.arr[i]!).floorRoot (((Array.finRange q).map (fun (k: Fin q) => if k.1 == i then 1 else pp.S_array.arr[k]! ^ aux.arr[k]!)).foldr (· * ·) 1))  % pp.N


def Verify {q: ℕ} (pp: PublicParameters q) (C m i proof : ℕ) : Bool :=
  if C == (pp.S_array.arr[i]! ^ m) * (proof ^ pp.e_array.arr[i]!) % pp.N then Bool.true else Bool.false


def Update {q: ℕ} (pp: PublicParameters q) (C m m' i: ℕ) : ℕ × UpdateInfo := 
  (C * pp.S_array.arr[i]!^(m' - m), {m := m, m' := m', i := i})

def ProofUpdate {q: ℕ} (pp: PublicParameters q) (C proof j m' i: ℕ) (U: UpdateInfo) : ℕ × ℕ :=
  if i != j then
    (C * pp.S_array.arr[i]!^(m' - U.m), proof * pp.e_array.arr[i]!.floorRoot (pp.S_array.arr[i]!^(m' - U.m)))
  else
    (C * pp.S_array.arr[i]!^(m' - U.m), proof)

