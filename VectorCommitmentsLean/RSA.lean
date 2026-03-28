import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ModEq
import Mathlib.FieldTheory.Finite.Basic 
import Mathlib.Tactic.Change
import Mathlib.Algebra.Order.Ring.Nat


-- variables (a b c d n : ℕ)
-- Helpers for proof
@[grind]
lemma mod_pow_mod (a b n : ℕ ): ((a % n) ^ b) % n = (a ^ b) % n  :=
  by
    change (a % n) ^ b ≡ (a ^ b) [MOD n]
    gcongr 
    apply Nat.mod_modEq

@[grind]
lemma mul_mod_right_distrib (a b n : ℕ) : (a * b) % n = ((a % n) * (b % n)) % n :=
  by
    change (a * b) ≡ a % n * (b % n) [MOD n]
    gcongr
    {apply Nat.ModEq.symm; exact Nat.mod_modEq _ _}
    {apply Nat.ModEq.symm; exact Nat.mod_modEq _ _}


-- variables (msg pub_e p q priv : ℕ)

-- Encryption
@[grind]
def enc (msg pub_e n: ℕ) : ℕ := (msg ^ pub_e) % n

@[grind]
def dec (enc priv n : ℕ) : ℕ := (enc ^ priv) % n
@[grind]
lemma mul_coprime_or_coprime_and {p q: ℕ} (msg: ℕ)
  (prime_p : p.Prime)
  (prime_q : q.Prime)
  : (p.Coprime msg ∧ q.Coprime msg) ∨ (¬p.Coprime msg ∨ ¬q.Coprime msg) := 
  by
    by_cases h : (p * q).Coprime msg
    {
      apply Or.inl
      apply And.intro
      exact Nat.Coprime.coprime_mul_right h
      exact Nat.Coprime.coprime_mul_left h
    }
    {
      apply Or.inr
      rw [Nat.Prime.not_coprime_iff_dvd] at h
      rcases h with ⟨k, prime_k, k_dvd_pq, k_dvd_msg⟩
      rw [Nat.Prime.dvd_mul prime_k] at k_dvd_pq
      cases k_dvd_pq with
      | inl k_dvd_p => 
        rw [Nat.dvd_prime prime_p] at k_dvd_p
        cases k_dvd_p with
        | inl k_one => have k_ne_one : k ≠ 1 := Nat.Prime.ne_one prime_k; contradiction
        | inr k_p => 
          rw [k_p] at k_dvd_msg
          apply Or.inl
          rw [← Nat.Prime.dvd_iff_not_coprime prime_p]
          assumption

      | inr k_dvd_q => 
        rw [Nat.dvd_prime prime_q] at k_dvd_q
        cases k_dvd_q with
        | inl k_one => have k_ne_one : k ≠ 1 := Nat.Prime.ne_one prime_k; contradiction
        | inr k_q => 
          rw [k_q] at k_dvd_msg
          apply Or.inr
          rw [← Nat.Prime.dvd_iff_not_coprime prime_q]
          assumption
    }

@[grind]
theorem dec_undoes_enc {p q n msg pub_e priv: ℕ}
-- These are the picking requirements
  (prime_p : p.Prime)
  (prime_q : q.Prime)
  
  (diff_pq : p ≠ q)
  (npq: n = p * q)  
  (one_lt_pub_e : 1 < pub_e)
  (msg_lt_pq : msg < (p * q))
  (pub_e_lt_totient : pub_e < (p * q).totient)
  (pub_e_coprime_totient : pub_e * priv ≡ 1 [MOD (p * q).totient])
  : msg = dec  (enc msg pub_e n) priv n := 
    by
      have msg_coprime_or_not := mul_coprime_or_coprime_and msg prime_p prime_q
      rw [enc, dec, mod_pow_mod, ← pow_mul]
      have msg_zero_or_gt : 0 = msg ∨ 0 < msg := Nat.eq_or_lt_of_le (Nat.zero_le msg)
      rw [Nat.ModEq.comm] at pub_e_coprime_totient
      have one_le_mul_pub_e_priv : 1 ≤ pub_e * priv
      := by
         apply Nat.ModEq.le_of_lt_add pub_e_coprime_totient _
         apply Nat.lt_add_left
         exact Nat.lt_trans one_lt_pub_e pub_e_lt_totient
      cases msg_zero_or_gt with 
      | inl eq_zero => rw [← eq_zero, zero_pow (by linarith)]; simp
      | inr gt_zero => 
        conv =>
          lhs
          rw [← Nat.mod_eq_of_lt msg_lt_pq]
        rw [npq]
        have p_coprime_q : p.Coprime q
          := (Nat.coprime_primes prime_p prime_q).mpr diff_pq        
        rw [←Nat.ModEq, ← Nat.modEq_and_modEq_iff_modEq_mul p_coprime_q]
        apply And.intro
        all_goals (
          rw [Nat.modEq_iff_dvd' one_le_mul_pub_e_priv] at pub_e_coprime_totient
          rcases pub_e_coprime_totient with ⟨k, h₁⟩
          have h₂ : (pub_e * priv - 1).succ = ((p * q).totient * k).succ        := congr_arg Nat.succ h₁
          rw [Nat.sub_one, Nat.succ_pred_eq_of_pos (Nat.lt_of_succ_le one_le_mul_pub_e_priv)] at h₂
          rw [h₂]
          rw [pow_succ, pow_mul, Nat.ModEq, mul_mod_right_distrib, ← mod_pow_mod]
        )
        show  msg % q = (msg ^ (p * q).totient % q) ^ k % q * (msg % q) % q
        rw [mul_comm p]
        show msg % p = (msg ^ (p * q).totient % p) ^ k % p * (msg % p) % p
        all_goals (
          rcases msg_coprime_or_not with coprime | ncoprime
          {
            first

            | have h₃ := Nat.ModEq.pow_totient (Nat.Coprime.pow_left q.totient (Nat.Coprime.symm coprime.1))
              rw [Nat.ModEq] at h₃
              have small_rewrite : msg ^ (p * q).totient = (msg ^ q.totient) ^ p.totient := 
                by
                  rw [Nat.totient_mul ((Nat.coprime_primes prime_p prime_q).mpr diff_pq), mul_comm]
                  apply pow_mul 
              rw [← small_rewrite] at h₃
              rw [h₃]
            | have h₃ := Nat.ModEq.pow_totient (Nat.Coprime.pow_left p.totient (Nat.Coprime.symm coprime.2))
              rw [Nat.ModEq] at h₃ 
              have small_rewrite : msg ^ (q * p).totient = (msg ^ p.totient) ^ q.totient := 
                by
                  rw [mul_comm, Nat.totient_mul ((Nat.coprime_primes prime_p prime_q).mpr diff_pq)]
                  apply pow_mul 
              rw [← small_rewrite] at h₃
              rw [h₃]
            repeat 
              (first
                | rw [Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_p)]
                | rw [Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_q)]
                | rw [one_pow])
            simp
          }
        )
        {
          rcases ncoprime with np | nq
          {
            rw [Nat.totient_mul p_coprime_q, pow_mul, ←mod_pow_mod _ q.totient]
            rw [← Nat.Prime.dvd_iff_not_coprime prime_p] at np
            rw [← Nat.modEq_zero_iff_dvd, Nat.ModEq] at np
            rw [mul_mod_right_distrib, np]
            simp
          }
          {
            have msg_coprime_p : msg.Coprime p :=
              by
                rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd prime_p]
                rw [←Nat.Prime.dvd_iff_not_coprime prime_q] at nq
                exact (by
                  intro p_dvd_msg
                  have pq_dvd_msg 
                    := Nat.Prime.dvd_mul_of_dvd_ne
                       diff_pq prime_p prime_q p_dvd_msg nq
                  have pq_not_dvd_msg 
                    := Nat.not_dvd_of_pos_of_lt gt_zero msg_lt_pq
                  contradiction
                )
            rw [Nat.totient_mul p_coprime_q, pow_mul, ←mod_pow_mod _ q.totient]
            have h₃ := Nat.ModEq.pow_totient msg_coprime_p
            rw [Nat.ModEq] at h₃
            rw [h₃]
            repeat (
              first
              | rw [Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_p)]
              | rw [one_pow]
            )
            simp
          }
        }
        {
          rcases ncoprime with np | nq
          {
            have msg_coprime_q : msg.Coprime q :=
              by
                rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd prime_q]
                rw [← Nat.Prime.dvd_iff_not_coprime prime_p] at np
                exact (by
                  intro q_dvd_msg
                  have pq_dvd_msg 
                    := Nat.Prime.dvd_mul_of_dvd_ne
                       diff_pq prime_p prime_q np q_dvd_msg
                  have pq_not_dvd_msg
                    := Nat.not_dvd_of_pos_of_lt gt_zero msg_lt_pq
                  exact absurd pq_dvd_msg pq_not_dvd_msg
                )
            rw [Nat.totient_mul (Nat.Coprime.symm p_coprime_q),
                pow_mul,
                ←mod_pow_mod _ p.totient]
            have h₃ := Nat.ModEq.pow_totient msg_coprime_q
            rw [Nat.ModEq] at h₃
            rw [h₃]
            repeat (
              first
              | rw [Nat.mod_eq_of_lt (Nat.Prime.one_lt prime_q)]
              | rw [one_pow]
            )
            simp
          }
          {
            rw [Nat.totient_mul (Nat.Coprime.symm p_coprime_q),
               pow_mul,
               ←mod_pow_mod _ p.totient]
            rw [←Nat.Prime.dvd_iff_not_coprime prime_q] at nq
            rw [←Nat.modEq_zero_iff_dvd, Nat.ModEq] at nq
            rw [mul_mod_right_distrib, nq]
            simp
          }
        }
        
structure RSA_Adversary where
  f: ℕ → ℕ → ℕ → ℕ
  proof: ∀ N e z, (f N e z) ^ e = z % N
