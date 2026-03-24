import VectorCommitmentsLean.RSA
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Tactic


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
    S_array := {arr := Array.ofFn (n := q) (fun i => a ^ (∏ j : Fin q,  if i.1 == j.1 then 1 else e_array.arr[j.1]'(by grind))), proof := by simp} 
  }
@[grind]
def Commitment {q: ℕ} (pp: PublicParameters q)(m_array: FixedArray q ℕ) : ℕ × Auxillary q := 
  (∏  i : Fin q,  pp.S_array.arr[i.1]'(by grind) ^ m_array.arr[i.1]'(by grind) , m_array)
@[grind]
def Open {q: ℕ} (pp: PublicParameters q) (_: ℕ) (i: ℕ) (aux : Auxillary q) (iValid: i < q) : ℕ :=
  ((pp.e_array.arr[i]'(by grind)).floorRoot 
    (∏ k: Fin q , (if k.1 == i then 1 else pp.S_array.arr[k.1]'(by grind) ^ aux.arr[k.1]'(by grind)))) % pp.N

@[grind]
def Verify {q: ℕ} (pp: PublicParameters q) (C m i proof : ℕ) (iValid: i < q): Bool :=
  if C == (pp.S_array.arr[i]'(by grind) ^ m) * (proof ^ pp.e_array.arr[i]'(by grind)) % pp.N then Bool.true else Bool.false

@[grind]
def Update {q: ℕ} (pp: PublicParameters q) (C m m' i: ℕ) (iValid: i < q): ℕ × UpdateInfo := 
  (C * (pp.S_array.arr[i]'(by grind))^(m' - m), {m := m, m' := m', i := i})
@[grind]
def ProofUpdate {q: ℕ} (pp: PublicParameters q) (C proof j m' i: ℕ) (U: UpdateInfo) (iValid: i < q) (jValid: j < q): ℕ × ℕ :=
  if i != j then
    (C * pp.S_array.arr[i]'(by grind)^(m' - U.m), proof * (pp.e_array.arr[i]'(by grind)).floorRoot (pp.S_array.arr[i]'(by grind)^(m' - U.m)))
  else
    (C * pp.S_array.arr[i]'(by grind)^(m' - U.m), proof)


lemma fin_prod_factor_out (q : ℕ) (e : Fin q → ℕ) (x i : Fin q) (hxi : x ≠ i) :
    ∏ j : Fin q, (if j = x then 1 else e j) =
    e i * ∏ j : Fin q, (if j = x ∨ j = i then 1 else e j) := by
  simp [ Finset.prod_ite, Finset.filter_ne', Finset.filter_or ]
  rw [ Finset.prod_eq_mul_prod_diff_singleton <| Finset.mem_erase_of_ne_of_mem hxi.symm <| Finset.mem_univ i ]
  rcongr j 
  aesop


lemma fin_prod_split (q : ℕ) (f : Fin q → ℕ) (i : Fin q) :
    ∏ x : Fin q, f x = f i * ∏ x : Fin q, if x = i then 1 else f x := by
  rw [ Finset.prod_ite ] 
  simp [ Finset.filter_ne' ]
  rw [ mul_comm, Finset.prod_erase_mul _ _ ( Finset.mem_univ _ ) ]

lemma prod_is_perfect_power (q : ℕ) (a : ℕ) (e m : Fin q → ℕ) (i : Fin q) :
    ∏ x : Fin q, (if x = i then 1 else (a ^ ∏ j : Fin q, if j = x then 1 else e j) ^ m x) =
    (∏ x : Fin q, (if x = i then 1 else (a ^ ∏ j : Fin q, if j = x ∨ j = i then 1 else e j) ^ m x)) ^ e i := by
  -- By fin_prod_factor_out, we can factor out e i from the product.
  have h_factor : ∀ x ≠ i, (a ^ (∏ j : Fin q, if j = x then 1 else e j)) ^ (m x) = ((a ^ (∏ j : Fin q, if j = x ∨ j = i then 1 else e j)) ^ (e i)) ^ (m x) := 
    by
      intros x hxi
      rw [ fin_prod_factor_out q e x i hxi, pow_mul' ]
  rw [ ← Finset.prod_pow ]
  apply Finset.prod_congr rfl
  intros x hx
  split_ifs with hi
  · simp
  · rw [h_factor x hi, ← pow_mul, ← pow_mul _ (m x), mul_comm (e i)]


lemma mul_mod_pow_mod (A B N n : ℕ) :
    (A * (B % N) ^ n) % N = (A * B ^ n) % N := by
  change (A * (B % N) ^ n) ≡ (A * B ^ n) [MOD N]
  gcongr
  apply Nat.mod_modEq



lemma if_neg_rewrite {α: Type} {c: Prop} [Decidable c] {e₁ e₂: α} (x: α) (h: ¬c → (e₂ = x)) : (if c then e₁ else e₂) = (if c then e₁ else x) :=
  by
    split_ifs
    rfl
    apply h; assumption

/-
PROVIDED SOLUTION
Step 1: Unfold Verify, KeyGen, Commitment, Open definitions using simp. Destructure validPublicKey, validCommitment. Substitute mCorrect (m = m_array[i]) and auxEq (m_array = aux). Substitute validProof (the proof value).

After unfolding, the goal becomes:
  C = (S_i ^ m_i * (floorRoot(e_i, P) % N) ^ e_i) % N
where:
  S_i = a ^ (∏ j, if i = j then 1 else e_j)
  C = ∏ x, S_x ^ m_x
  P = ∏ x, if x = i then 1 else S_x ^ m_x
  N = p₁ * p₂

Step 2: By fin_prod_split, C = S_i ^ m_i * P.

Step 3: By prod_is_perfect_power, P = Y ^ e_i for some Y. Therefore floorRoot(e_i, P) = floorRoot(e_i, Y ^ e_i) = Y by Nat.floorRoot_pow_self (need e_i ≠ 0, which follows from 1 < e_i from the he hypothesis).

Step 4: By mul_mod_pow_mod, (S_i^m_i * (Y % N)^e_i) % N = (S_i^m_i * Y^e_i) % N = (S_i^m_i * P) % N = C % N = C (by Nat.mod_eq_of_lt and c_less).
-/
theorem normal_correctness {q: ℕ}
  (pp: PublicParameters q)
  (C: ℕ)
  (aux : Auxillary q)
  (m i: ℕ)
  (m_array: FixedArray q ℕ)
  (iValid: i < q)
  (proof: ℕ)
  (validPublicKey: ∃ p₁ p₂  a e_array neq hp₁ hp₂ he, KeyGen p₁ p₂ q a e_array neq hp₁ hp₂  he = pp)
  (validCommitment:  Commitment pp m_array = (C, aux))
  (validProof: Open pp m i aux  iValid = proof)
  (c_less: C < pp.N)
  :  m == m_array.arr[i]'(by rw [m_array.proof]; exact iValid) → Verify pp C m i proof iValid == Bool.true:=
    by
      intro mCorrect
      rcases validPublicKey with ⟨ p₁, p₂, a, e_array, neq, hp₁, hp₂, he, rfl⟩
      simp_all [ Commitment, Open ] 
      -- By `fin_prod_split`, `C` can be written as `S_i ^ m_i * P`.
      have hC_split : C = (a ^ (∏ j : Fin q, if i = j then 1 else e_array.arr[j]'(by
      simp [ e_array.proof ]))) ^ m_array.arr[i]'(by
      simpa [ m_array.proof ] using iValid) * ∏ x : Fin q, (if x = i then 1 else (a ^ (∏ j : Fin q, if x = j then 1 else e_array.arr[j]'(by
      simp  [ e_array.2 ]))) ^ m_array.arr[x]'(by
      exact m_array.proof.symm ▸ x.2)) := by
        rw [ ← validCommitment.1, fin_prod_split ];
        swap;
        exact ⟨ i, iValid ⟩;
        simp  [ Fin.ext_iff, KeyGen ]
      generalize_proofs at *;
      -- By `prod_is_perfect_power`, `P` can be written as `Y ^ e_i`.
      obtain ⟨Y, hY⟩ : ∃ Y, ∏ x : Fin q, (if x = i then 1 else (a ^ (∏ j : Fin q, if x = j then 1 else e_array.arr[j]'(by
      grind))) ^ m_array.arr[x]'(by
      grind)) = Y ^ e_array.arr[i]'(by
      assumption) := by
        use ∏ x : Fin q, (if x = i then 1 else (a ^ (∏ j : Fin q, if x = j ∨ i = j then 1 else e_array.arr[j]'(by
        grind))) ^ m_array.arr[x]'(by
        grind))
        generalize_proofs at *;
        convert prod_is_perfect_power q a ( fun j => e_array.arr[j]'(by
        grind) ) ( fun j => m_array.arr[j]'(by
        grind) ) ⟨ i, iValid ⟩ using 1
        all_goals generalize_proofs at *;
        · simp  [ Fin.ext_iff, eq_comm ];
        · simp  [ Fin.ext_iff, eq_comm ]
      generalize_proofs at *;
      -- By `Nat.floorRoot_pow_self`, `floorRoot(e_i, Y ^ e_i) = Y`.
      have h_floorRoot : Nat.floorRoot (e_array.arr[i]'(by
      assumption)) (Y ^ e_array.arr[i]'(by
      assumption)) = Y := by
        apply Nat.floorRoot_pow_self;
        exact ne_of_gt ( lt_trans zero_lt_one ( he _ ( by simp ) |>.2.1 ) )
      generalize_proofs at *;
      -- Substitute `Y` for `proof` in the goal.
      have h_proof : proof = Y % (p₁ * p₂) := by
        rw [ ← validProof, ← h_floorRoot, ← hY ];
        simp  [ KeyGen, Finset.prod_ite, validCommitment.2 ];
        simp  [ Fin.ext_iff ];
      unfold Verify; simp  [ hC_split, h_proof ] ;
      convert congr_arg ( · % ( p₁ * p₂ ) ) hC_split using 1;
      · rw [ hC_split, Nat.mod_eq_of_lt ];
        · congr! 3;
        · exact hC_split ▸ c_less;
      · simp [ KeyGen, Nat.mul_mod, Nat.pow_mod ];
        simp [ ← Nat.pow_mod, validCommitment.2.symm ];
        simp [ ← hY ];


-- theorem normal_correctness {q: ℕ} 
--   (pp: PublicParameters q)
--   (C: ℕ)
--   (aux : Auxillary q)
--   (m i: ℕ)
--   (m_array: FixedArray q ℕ)
--   (iValid: i < q)
--   (proof: ℕ)
--   (validPublicKey: ∃ p₁ p₂  a e_array neq hp₁ hp₂ he, KeyGen p₁ p₂ q a e_array neq hp₁ hp₂  he = pp)
--   (validCommitment:  Commitment pp m_array = (C, aux))
--   (validProof: Open pp m i aux  iValid = proof)
--   (c_less: C < pp.N)
--   :  m == m_array.arr[i]'(by rw [m_array.proof]; exact iValid) → Verify pp C m i proof iValid == Bool.true:= 
--     by
--       intro mCorrect 
--       rcases validPublicKey with ⟨p₁, p₂, a, e_array, neq, hp₁, hp₂, he, validPublicKey⟩
--       simp [Verify]
--       simp [KeyGen] at validPublicKey
--       simp [Commitment] at validCommitment
--       simp [Open] at validProof
--       cases validPublicKey
--       simp at *
--       rcases validCommitment with ⟨cEq, auxEq⟩
--       sorry
