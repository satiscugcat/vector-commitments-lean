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
      rcases validPublicKey with ⟨p₁, p₂, a, e_array, neq, hp₁, hp₂, he, validPublicKey⟩
      simp [Verify]
      simp [KeyGen] at validPublicKey
      simp [Commitment] at validCommitment
      simp [Open] at validProof
      cases validPublicKey
      simp at *
      rcases validCommitment with ⟨cEq, auxEq⟩
      -- rewriting cEq
      conv at cEq =>
        left
        rw [fin_prod_split _ _ ⟨i, iValid⟩]
        simp [Fin.ext_iff]
      
      have : _ := fun  m => prod_is_perfect_power q a (fun x_1 => e_array.arr[↑x_1]'(by grind)) m ⟨i, iValid⟩       
      simp [Fin.ext_iff] at this
      conv at this =>
        intro m
        left; right
        intro x
        right; left; right; right
        intro x_1
        simp [eq_comm]
        
      conv at validProof =>
        left; left; right
        simp [Fin.ext_iff]; rw [this]
        left; right; intro _; right; right; rw [← auxEq]
      conv at cEq =>
        left; right
        simp [Fin.ext_iff]; rw [this]
      rw [Nat.floorRoot_pow_self (by exact ne_of_gt (lt_trans zero_lt_one (he _ ( by simp ) |>.2.1 ) ))] at validProof
      conv =>
        right; left
        rw [mCorrect]
        rw [← validProof]
      conv =>
        right
        rw [mul_mod_pow_mod]
        left
        rw [cEq]      
      exact Eq.symm (Nat.mod_eq_of_lt c_less)



theorem update_correctness {q: ℕ} 
  (pp: PublicParameters q)
  (C C': ℕ)
  (aux : Auxillary q)
  (m m' i j: ℕ)
  (m_array: FixedArray q ℕ)
  (jValid: j < q)
  (iValid: i < q)
  (updateGreater: m' > m)
  (proof proof': ℕ)
  (u: UpdateInfo)
  (validPublicKey: ∃ p₁ p₂  a e_array neq hp₁ hp₂ he, KeyGen p₁ p₂ q a e_array neq hp₁ hp₂  he = pp)
  (validCommitment:  Commitment pp m_array = (C, aux))
  (validProof: Open pp m j aux jValid = proof)
  (validNewCommitment: Update pp C m m' i iValid = (C', u))
  (validNewProof: ProofUpdate pp C proof j m' i u iValid jValid = (proof', C'))
  (c'_less: C' < pp.N)
  (c_less: C < pp.N)
  :  m == m_array.arr[i]'(by rw [m_array.proof]; exact iValid) → Verify pp C' m' i proof' iValid == Bool.true:= 
    by
      intro mCorrect 
      rcases validPublicKey with ⟨p₁, p₂, a, e_array, neq, hp₁, hp₂, he, validPublicKey⟩
      simp [Verify]
      simp [KeyGen] at validPublicKey
      simp [Commitment] at validCommitment
      simp [Open] at validProof
      simp [Update] at validNewCommitment
      simp [ProofUpdate] at validNewProof
      cases validPublicKey
      simp at *
      
      rcases validCommitment with ⟨cEq, auxEq⟩
      rcases validNewCommitment with ⟨c'Eq, uEq⟩
      cases uEq
      simp at *
      
      -- -- rewriting cEq
      -- conv at cEq =>
      --   left
      --   rw [fin_prod_split _ _ ⟨i, iValid⟩]
      --   simp [Fin.ext_iff]
      
      -- have : _ := fun  m => prod_is_perfect_power q a (fun x_1 => e_array.arr[↑x_1]'(by grind)) m ⟨i, iValid⟩       
      -- simp [Fin.ext_iff] at this
      -- conv at this =>
      --   intro m
      --   left; right
      --   intro x
      --   right; left; right; right
      --   intro x_1
      --   simp [eq_comm]
        
      -- conv at validProof =>
      --   left; left; right
      --   simp [Fin.ext_iff]; rw [this]
      --   left; right; intro _; right; right; rw [← auxEq]
      -- conv at cEq =>
      --   left; right
      --   simp [Fin.ext_iff]; rw [this]
      -- rw [Nat.floorRoot_pow_self (by exact ne_of_gt (lt_trans zero_lt_one (he _ ( by simp ) |>.2.1 ) ))] at validProof
      -- conv =>
      --   right; left
      --   rw [mCorrect]
      --   rw [← validProof]
      -- conv =>
      --   right
      --   rw [mul_mod_pow_mod]
      --   left
      --   rw [cEq]      
      -- exact Eq.symm (Nat.mod_eq_of_lt c_less)
      sorry

structure VC_Adversary (q: ℕ) where
  A: PublicParameters q → (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)
  iq: ∀ pp, (A pp).2.2.2.1 < q
  proof: ∀ pp,  Verify pp (A pp).1 (A pp).2.1 (A pp).2.2.2.1 (A pp).2.2.2.2.1 (iq pp) = Bool.true 
                ∧ Verify pp (A pp).1 (A pp).2.2.1 (A pp).2.2.2.1 (A pp).2.2.2.2.2 (iq pp) = Bool.true
                ∧ (A pp).2.1 ≠ (A pp).2.2.1
/-
  We need to construct an RSA adversary from a vector commitment adversary. All the pain points have exclamation marks beside them.
  The proof in the paper takes the following steps:
  1. Let the inputs to RSA Adversary be N, z, e. We need a value y.
  2. Randomly choose an index to put our e in. Assign a to z. Generate the rest as required by KeyGen.
     Note that we do NOT use N. We can use whatever prime numbers we wish.
  3. Now, we get (C, m, m', i, P, P') according to VC adversary. 
  4. If we put e at this i, then fine, else discard. [!! We do not have randomness. Have to add as an assumption]
  5. From the equations C = S_i^m P^{e_i} C = S_i^m' P'^{e_i}: [!! Do we have this? Yes. If C < pq, then p is necessarily lesser than pq. We can always choose pq large enough.]
  6. S_i^{m-m'}=(P'/P)^{e_i}
  7. If RHS is 1, then we can factor with non-neglible probability. [!! Cited paper, we have to add as an assumption. Also change probability to guarantee? This feels weird to assume.]
  8. If RHS is not 1, we can apply Shamir's trick. [!! Cited paper. Do we need to assume?]
  9. Since gcd(m ∏_{i ≠ j} e_j, e_i) = 1 (why?) compute integers λ μ such that linear combination is 1.
  10. Leads to equation a = Λ^{λe_i}a^{μe_i}. 
-/
def vc_secure{q: ℕ} (vc: VC_Adversary q):  RSA_Adversary := sorry
