import Mathlib

open Nat Finset BigOperators
--======================================================================================
section Section1_Definitions
--======================================================================================
/-- 
Global definitions for the quotient (k) and residue (m) of an integer x modulo 2^v.
-/
def k (v x : ℕ) : ℕ := x / 2^v
def m (v x : ℕ) : ℕ := x % 2^v

/-- 
Theorem: Bounds of the Residue.
Establishes that for any odd integer x and positive integer v, 
the residue m(v, x) is bounded: 0 < m(v, x) ≤ 2^v - 1.
-/
theorem m_bounds (v x : ℕ) (hv : 1 ≤ v) (h_odd : Odd x) :
  0 < m v x ∧ m v x ≤ 2^v - 1 := by
  
  -- Establish positivity of the modulus
  have h_pow_pos : 0 < 2^v := pow_pos (by decide) v

  constructor
  · -- Lower Bound: Proves the residue cannot be zero for an odd integer.
    apply pos_of_ne_zero
    intro h_zero
    
    have h_div : 2^v ∣ x := dvd_of_mod_eq_zero h_zero
    
    have h_two_dvd_pow : 2 ∣ 2^v := by
      cases v with
      | zero => linarith
      | succ n => 
        use 2^n
        rw [pow_succ, mul_comm]

    -- Transitivity yields a contradiction with the odd parity of x
    have h_two_dvd_x : 2 ∣ x := dvd_trans h_two_dvd_pow h_div
    rw [Nat.odd_iff] at h_odd
    rw [dvd_iff_mod_eq_zero] at h_two_dvd_x
    rw [h_two_dvd_x] at h_odd
    contradiction

  · -- Upper Bound: Derived directly from modulo properties.
    have h_lt : x % 2^v < 2^v := mod_lt x h_pow_pos
    exact le_pred_of_lt h_lt

end Section1_Definitions
#print axioms m_bounds
#check m_bounds
-- ===============================================================
-- SECTION 1: THE COLLATZ OPERATOR (Multiple Iterations)
-- ===============================================================
section Section2_MultipleIterations

/-- 
Definition of the 2-adic valuation.
Extracts the exact power of 2 dividing 3x + 1. 
-/
noncomputable def val (x : ℕ) : ℕ := (Nat.factorization (3 * x + 1)) 2

/-- 
The Accelerated Collatz Odd-to-Odd Operator.
Represents the transformation: T(x) = (3x + 1) / 2^(val(x))
-/
noncomputable def T (x : ℕ) : ℕ :=
  (3 * x + 1) / (2 ^ (val x))

/-- 
Single Step Modular Expansion.
Formalizes the algebraic transition using the defined quotient and residue.
-/
theorem step_expansion (v x : ℕ) :
  T x = (3 * (2^v * (k v x)) + 3 * (m v x) + 1) / 2^(val x) := by
  
  dsimp [T]
  
  have h_decomp : x = 2^v * (k v x) + (m v x) := (Nat.div_add_mod x (2^v)).symm
  nth_rw 1 [h_decomp]
  
  congr 1
  ring
#check step_expansion
/-- 
The Collatz Operator Output Parity.
Proves that the accelerated Collatz operator T(x) always outputs an odd integer.
Any even output wouldviolate the absolute maximum factorization bound of the 2-adic valuation.
-/
theorem T_is_always_odd (x : ℕ) : (T x) % 2 = 1 := by
  
  have h_nz : 3 * x + 1 ≠ 0 := by omega
  have h_prime : Nat.Prime 2 := Nat.prime_two
  
  dsimp [T]
  
  by_contra h_not_odd
  
  have h_even : (3 * x + 1) / 2^(val x) % 2 = 0 := by omega
  
  have h_dvd_T : 2 ∣ (3 * x + 1) / 2^(val x) := Nat.dvd_of_mod_eq_zero h_even
  
  have h_dvd_next : 2^(val x + 1) ∣ 3 * x + 1 := by
    have h_div_cancel : 2^(val x) * ((3 * x + 1) / 2^(val x)) = 3 * x + 1 := by
      have h_div : 2^(val x) ∣ (3 * x + 1) := by
        rw [Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz]
        exact le_refl _
      exact Nat.mul_div_cancel' h_div
    
    -- Extract witness 'c' for the divisibility condition
    rcases h_dvd_T with ⟨c, hc⟩
    use c
    calc 3 * x + 1 = 2^(val x) * ((3 * x + 1) / 2^(val x)) := h_div_cancel.symm
      _ = 2^(val x) * (2 * c) := by rw [hc]
      _ = (2^(val x) * 2) * c := by ring
      _ = 2^(val x + 1) * c := by rw [← pow_succ]

  have h_max : val x + 1 ≤ (Nat.factorization (3 * x + 1)) 2 := 
    (Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz).mp h_dvd_next
  
  have h_val_def : (Nat.factorization (3 * x + 1)) 2 = val x := by rfl
  
  rw [h_val_def] at h_max
  
  omega

end Section2_MultipleIterations

#print axioms step_expansion
#print axioms T_is_always_odd
#check T_is_always_odd
-- ===============================================================
-- SECTION 3: RECURSIVE SEQUENCE AND EXPANSION
-- ===============================================================
section Section3_Recursive

/--
Exactness of the Collatz Step.
Establishes that 2^(val(x)) * T(x) = 3x + 1, representing the inverse of the division operation.
-/
theorem collatz_step_exact (x : ℕ) : 2^(val x) * T x = 3 * x + 1 := by
  dsimp [T]
  have h_prime : Nat.Prime 2 := Nat.prime_two
  
  have h_nz : 3 * x + 1 ≠ 0 := by omega
  
  have h_div : 2^(val x) ∣ (3 * x + 1) := by
    rw [Nat.Prime.pow_dvd_iff_le_factorization h_prime h_nz]
    exact le_refl _
  rw [mul_comm]
  rw [Nat.div_mul_cancel h_div]
#check collatz_step_exact
/--
Recursive Sum of Exponents (S_n).
S n x evaluates the cumulative sum of 2-adic valuations after n steps starting from x.
-/
noncomputable def S (n : ℕ) (x : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | succ k => S k x + val ((T^[k]) x)

/--
The Recursive Numerator (Z_n).
Defines the numerator component of the multi-step sequence: Z_0 = 0, Z_{k+1} = 3*Z_k + 2^{S_k}.
-/
noncomputable def closed_numerator (n : ℕ) (x : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | succ k => 3 * (closed_numerator k x) + 2^(S k x)

/--
The Fundamental Iteration Formula.
Formulates the core algebraic expansion of the trajectory: 2^(S_n) * x_n = 3^n * x + Z_n.
-/
theorem iterate_expansion (n : ℕ) (x : ℕ) :
  2^(S n x) * (T^[n] x) = 3^n * x + closed_numerator n x := by
  
  induction n with
  | zero =>
    simp [S, closed_numerator]
  
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    let x_k := T^[k] x
    
    dsimp [S, closed_numerator]
    rw [pow_add]
    
    rw [mul_assoc]
    rw [collatz_step_exact x_k]
    
    rw [mul_add, mul_one]
    rw [mul_left_comm (2^(S k x)) 3 x_k]
    
    rw [ih]
    ring
#check iterate_expansion
/--
The Multi-Step Modular Diophantine Equation.
Substitutes the global modular definition (x = 2^v * k + m) into the fundamental iteration formula.
-/
theorem iterate_expansion_modular (n v x : ℕ) :
  2^(S n x) * (T^[n] x) = 3^n * (2^v * k v x + m v x) + closed_numerator n x := by
  have h_iter := iterate_expansion n x
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  rw [h_x]
  exact h_iter

end Section3_Recursive
#check iterate_expansion_modular
#print axioms collatz_step_exact
#print axioms iterate_expansion
#print axioms iterate_expansion_modular

-- ===============================================================
-- SECTION 4: CYCLE ANALYSIS
-- ===============================================================
section Section4_CycleAnalysis

/--
The Cycle Predicate.
Defines a cycle of length n as a trajectory where the n-th iterate equals the initial integer x.
-/
def is_cycle (n : ℕ) (x : ℕ) : Prop :=
  T^[n] x = x

/--
Cycle Parity Condition.
Establishes that any integer x forming a closed Collatz cycle must be odd. 
This condition ensures consistent baseline valuation bounds for the trajectory.
-/
theorem cycle_implies_odd (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) : 
  x % 2 = 1 := by
  
  cases n with
  | zero => 
    omega
  | succ k =>
    unfold is_cycle at h_cycle
    
    rw [Function.iterate_succ_apply'] at h_cycle
    
    have h_T_odd := T_is_always_odd (T^[k] x)
    
    rw [h_cycle] at h_T_odd
    
    exact h_T_odd

#check cycle_implies_odd
#print axioms cycle_implies_odd

/--
The Cycle Diophantine Equation.
Formulates the algebraic loop structure: if x forms a cycle, then (2^S - 3^n) * x = Z_n.
-/
theorem cycle_implies_diophantine (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * x = closed_numerator n x := by
  
  have h_fund := iterate_expansion n x
  rw [h_cycle] at h_fund
  
  rw [add_comm] at h_fund
  
  have h_sub : 2^(S n x) * x - 3^n * x = closed_numerator n x := 
    Nat.sub_eq_of_eq_add h_fund
  
  rw [← Nat.mul_sub_right_distrib] at h_sub
  
  exact h_sub

#check cycle_implies_diophantine
#print axioms cycle_implies_diophantine

end Section4_CycleAnalysis

-- ===============================================================
-- SECTION 5: LEMMA 1A SUPPLEMENT
-- ===============================================================
section Section5_Lemma1A_Supplement

/--
Equilibrium Exponent Derivation.
Proves that an equilibrium cycle ratio forces the uniform division exponent p to equal 2.
-/
theorem derivation_of_equilibrium_exponent (p R : ℕ) 
  (h_R_pos : 0 < R)
  (h_ratio : (R : ℤ) * ((2 : ℤ)^p - 3) = 1) : 
  p = 2 := by
  
  have h_R_ge_1 : (R : ℤ) ≥ 1 := by exact_mod_cast h_R_pos
  set X := (2 : ℤ)^p - 3
  
  have h_X_ge_1 : X ≥ 1 := by
    by_contra h_not
    
    have h_X_le_0 : X ≤ 0 := by omega 
    
    have h_prod_le_0 : (R : ℤ) * X ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by omega) h_X_le_0
    linarith
    
  have h_R_eq_1 : (R : ℤ) = 1 := by
    by_contra h_not
    have h_R_ge_2 : (R : ℤ) ≥ 2 := by omega
    have h_R_le_1 : (R : ℤ) ≤ 1 := by
      calc (R : ℤ) = (R : ℤ) * 1 := by ring
        _ ≤ (R : ℤ) * X := mul_le_mul_of_nonneg_left h_X_ge_1 (by omega)
        _ = 1 := h_ratio
    omega
    
  have h_X_eq_1 : X = 1 := by
    calc X = 1 * X := by ring
      _ = (R : ℤ) * X := by rw [h_R_eq_1]
      _ = 1 := h_ratio
      
  have h_pow : (2 : ℤ)^p = 4 := by 
    calc (2 : ℤ)^p = X + 3 := by dsimp [X]; ring
      _ = 1 + 3 := by rw [h_X_eq_1]
      _ = 4 := by ring
      
  have h_pow_nat : 2^p = 4 := by exact_mod_cast h_pow
  
  have h_not_lt : ¬ (p < 2) := by
    intro h_lt
    interval_cases p
    · norm_num at h_pow_nat
    · norm_num at h_pow_nat
    
  have h_not_gt : ¬ (p > 2) := by
    intro h_gt
    have h_bound : 2^p ≥ 8 := by
      calc 2^p ≥ 2^3 := Nat.pow_le_pow_right (by norm_num) h_gt
        _ = 8 := by rfl
    omega

  omega

#check derivation_of_equilibrium_exponent
#print axioms derivation_of_equilibrium_exponent

end Section5_Lemma1A_Supplement

-- ===============================================================
-- SECTION 6: LEMMA 1A (The Trivial Solution & The Contrapositive Bridge)
-- ===============================================================
section Section6_Lemma1A

/-- Equilibrium Denominator -/
def D_eq (n : ℕ) : ℕ := 2^(2 * n) - 3^n

/-- Equilibrium Numerator -/
def N_eq (n : ℕ) : ℕ := 4^n - 3^n

/-- 
Equilibrium Exponent Sum (S_n = 2n).
Proves the sequence prefix sum evaluates to 2n if all valuations equal 2. 
-/
lemma S_all_two (n : ℕ) (x : ℕ) (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  S n x = 2 * n := by
  induction n with
  | zero => simp [S]
  | succ k ih =>
    simp [S]
    have h_sub : ∀ j < k, val (T^[j] x) = 2 := fun j hj => h_all j (Nat.lt_succ_of_lt hj)
    rw [ih h_sub, h_all k (Nat.lt_succ_self k)]
    ring

#check S_all_two
#print axioms S_all_two

/-- 
Equilibrium Numerator (Z_n = N_eq).
Proves the recursive sequence geometrically expands to N_eq under the equilibrium constraint.
-/
lemma Z_all_two (n : ℕ) (x : ℕ) (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  closed_numerator n x = N_eq n := by
  induction n with
  | zero => simp [closed_numerator, N_eq]
  | succ k ih =>
    simp [closed_numerator]
    
    have h_sub : ∀ j < k, val (T^[j] x) = 2 := fun j hj => h_all j (Nat.lt_succ_of_lt hj)
    rw [ih h_sub, S_all_two k x h_sub]
    rw [pow_mul, show 2^2 = 4 by rfl]
    
    unfold N_eq
    symm
    
    -- Establish inequality of the respective base powers
    have h_le_pow_succ : 3^(k+1) ≤ 4^(k+1) := Nat.pow_le_pow_left (by norm_num) (k+1)
    rw [Nat.sub_eq_iff_eq_add h_le_pow_succ]
    
    rw [Nat.mul_sub_left_distrib 3 (4^k) (3^k)]
    
    rw [pow_succ' 4 k, pow_succ' 3 k]
    rw [add_assoc, add_comm (4^k), ← add_assoc]
    
    have h_inner_le : 3^k ≤ 4^k := Nat.pow_le_pow_left (by norm_num) k
    have h_cancel_le : 3 * 3^k ≤ 3 * 4^k := Nat.mul_le_mul_left 3 h_inner_le
    rw [Nat.sub_add_cancel h_cancel_le]
    ring

#check Z_all_two
#print axioms Z_all_two

/--
The Modular Cycle Diophantine Equation.
Forces the cycle structure to account for the quotient and residue parameters.
-/
theorem cycle_implies_diophantine_modular (n v x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * (2^v * k v x + m v x) = closed_numerator n x := by
  have h_eqn := cycle_implies_diophantine n x h_cycle
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  rw [h_x]
  exact h_eqn

#check cycle_implies_diophantine_modular
#print axioms cycle_implies_diophantine_modular

/--
Lemma 1A (The Trivial Solution - Integrated Modular Form)
Proves x = 1. This theorem utilizes the modular cycle Diophantine equation, 
evaluating the trajectory by resolving x into its quotient (k) and residue (m) parameters.
-/
theorem lemma_1a_trivial_solution (n : ℕ) (x : ℕ) 
  (h_cycle : is_cycle n x) 
  (h_pos : n > 0)
  (h_all : ∀ k < n, val (T^[k] x) = 2) : 
  x = 1 := by
  
  let v := 2 * n
  have h_eqn := cycle_implies_diophantine_modular n v x h_cycle
  
  rw [S_all_two n x h_all, Z_all_two n x h_all] at h_eqn
  dsimp [D_eq, N_eq] at h_eqn
  
  rw [pow_mul, show 2^2 = 4 by rfl] at h_eqn

  have h_nonzero : 0 < 4^n - 3^n := 
    Nat.sub_pos_of_lt (Nat.pow_lt_pow_left (by norm_num) (Nat.ne_of_gt h_pos))
  
  conv_rhs at h_eqn => rw [← mul_one (4^n - 3^n)]
  
  have h_modular_one := Nat.eq_of_mul_eq_mul_left h_nonzero h_eqn
  
  have h_x : 2^v * k v x + m v x = x := by
    dsimp [k, m]
    exact Nat.div_add_mod x (2^v)
  
  have h_align : 4^n = 2^v := by
    have h_four : 4 = 2^2 := by rfl
    rw [h_four, ← pow_mul]
  
  rw [h_align] at h_modular_one
  
  rw [h_x] at h_modular_one
  exact h_modular_one

#check lemma_1a_trivial_solution
#print axioms lemma_1a_trivial_solution

/--
The Non-Trivial Contrapositive (The Logical Bridge).
Proves that any closed cycle originating at x > 1 
cannot maintain the equilibrium sequence of valuations.
This creates the mathematical bridge out of the trivial state,
forcing all non-trivial cycles into the perturbed domain.
-/
theorem non_trivial_cycle_forces_perturbation (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn_pos : n > 0)
  (h_non_trivial : x > 1) :
  ¬ (∀ k < n, val (T^[k] x) = 2) := by
  
  intro h_all_two
  have h_x_eq_1 := lemma_1a_trivial_solution n x h_cycle hn_pos h_all_two
  
  -- The trivial solution x = 1 creates a mathematical contradiction with x > 1
  omega

#check non_trivial_cycle_forces_perturbation
#print axioms non_trivial_cycle_forces_perturbation

end Section6_Lemma1A

-- ===============================================================
-- SECTION 7: THE EXISTENCE THRESHOLD
-- ===============================================================
section Section7_Existence_Threshold

/--
Corollary 1A.1: The Existence Threshold.
Proves that cycle existence requires the geometric denominator 2^S - 3^n to remain positive.
-/
theorem cycle_existence_threshold (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  3^n < 2^(S n x) := by
  
  have h_eqn := cycle_implies_diophantine n x h_cycle
  
  have h_pos_Zn : 0 < closed_numerator n x := by
    cases n with
    | zero => 

      omega
    | succ k => 
      unfold closed_numerator
      apply Nat.add_pos_right
      apply Nat.pow_pos
      norm_num

  have h_mul_pos : 0 < (2^(S n x) - 3^n) * x := by 
    rw [h_eqn]
    exact h_pos_Zn
    
  have h_sub_pos : 0 < 2^(S n x) - 3^n := 
    Nat.pos_of_mul_pos_right h_mul_pos

  exact Nat.lt_of_sub_pos h_sub_pos

#check cycle_existence_threshold
#print axioms cycle_existence_threshold
end Section7_Existence_Threshold

-- ===============================================================
-- SECTION 8: THE GEOMETRIC SUMMATION
-- ===============================================================
section Section8_Lemma2A_Explicit

/--
The Summation T_n.
Translates the recursive numerator into a geometric series.
-/
noncomputable def sum_T (n : ℕ) (x : ℕ) : ℕ :=
  ∑ k ∈ range n, 3^(n - 1 - k) * 2^(S k x)

/--
Equivalence of Recursive Forms.
Proves Z_n = sum_T(n, x), ensuring the algebraic transition is rigorous.
-/
theorem closed_numerator_eq_sum_T (n : ℕ) (x : ℕ) :
  closed_numerator n x = sum_T n x := by
  induction n with
  | zero =>
    simp [closed_numerator, sum_T]
  | succ k ih =>
    rw [closed_numerator, ih]
    dsimp [sum_T]
    
    rw [sum_range_succ]
    
    rw [Nat.sub_self, pow_zero, one_mul]
    
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro j hj
    
    rw [← mul_assoc, mul_comm 3 (3^(k - 1 - j)), ← pow_succ]
    congr 2
    
    -- Simplifies the exponent using the upper bound of the summation index
    have h_lt : j < k := Finset.mem_range.mp hj
    omega
#check closed_numerator_eq_sum_T
/--
The Cycle Diophantine Identity.
Substitutes the geometric sum into the fundamental cycle equation.
-/
theorem cycle_implies_explicit_diophantine (n : ℕ) (x : ℕ) (h_cycle : is_cycle n x) :
  (2^(S n x) - 3^n) * x = sum_T n x := by
  have h_orig := cycle_implies_diophantine n x h_cycle
  rw [closed_numerator_eq_sum_T n x] at h_orig
  exact h_orig

end Section8_Lemma2A_Explicit

#print axioms closed_numerator_eq_sum_T
#print axioms cycle_implies_explicit_diophantine
#check cycle_implies_explicit_diophantine

-- ===============================================================
-- SECTION 9: THE PERTURBATION MODEL
-- ===============================================================

section Section9_Perturbation_Model

/--
Index Shift Identity.

Algebraic form:
`(m + 1) - 1 - j = (m - 1 - j) + 1` for `j < m`.
-/
lemma nat_index_shift (m j : ℕ) (hj : j < m) :
  m + 1 - 1 - j = (m - 1 - j) + 1 := by
  omega

/--
Equilibrium Numerator Summation Identity.

Formulates:
`4^n - 3^n = Σ_{j=0}^{n-1} 3^(n-1-j) * 2^(2j)`.
-/
theorem N_eq_as_sum (n : ℕ) :
  (N_eq n : ℚ) =
    ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by

  rw [N_eq]

  induction n with
  | zero =>
      simp

  | succ m ih =>
      rw [sum_range_succ]

      have h_factor :
          ∑ j ∈ range m,
              (3 : ℚ)^(m.succ - 1 - j) * (2 : ℚ)^(2 * j)
            =
          3 * ∑ j ∈ range m,
              (3 : ℚ)^(m - 1 - j) * (2 : ℚ)^(2 * j) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j hj
        rw [nat_index_shift m j (Finset.mem_range.mp hj), pow_succ]
        ring

      rw [h_factor, ← ih]

      have h_pow_match :
          (2 : ℚ)^(2 * m) = (4 : ℚ)^m := by
        rw [pow_mul]
        norm_num

      simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul, h_pow_match]

      have h_le_succ : 3^(m + 1) ≤ 4^(m + 1) :=
        Nat.pow_le_pow_left (by norm_num) (m + 1)

      have h_le_m : 3^m ≤ 4^m :=
        Nat.pow_le_pow_left (by norm_num) m

      rw [Nat.cast_sub h_le_succ, Nat.cast_sub h_le_m]
      push_cast
      ring

/--
The local perturbation operator.

`δᵢ = aᵢ - 2`, where `aᵢ = val (T^[i] x)`.
-/
noncomputable def delta (x : ℕ) (i : ℕ) : ℤ :=
  (val (T^[i] x) : ℤ) - 2

/--
Prefix sum of perturbations.

`S'_j = Σ_{i=0}^{j-1} δᵢ`.
-/
noncomputable def S_prime (j : ℕ) (x : ℕ) : ℤ :=
  ∑ i ∈ range j, delta x i

/--
Prefix Sum Equivalence.

The actual exponent sum equals the equilibrium baseline plus cumulative
perturbation:
`S_j = 2j + S'_j`.
-/
theorem s_relationship (j : ℕ) (x : ℕ) :
  (S j x : ℤ) = 2 * (j : ℤ) + S_prime j x := by

  induction j with
  | zero =>
      simp [S, S_prime]

  | succ n ih =>
      simp [S, S_prime, sum_range_succ, ih]
      dsimp [delta]
      ring

/--
The Exact Difference Formula.

This expresses the numerator deviation from equilibrium as a weighted
perturbation sum.
-/
theorem exact_difference_formula (n : ℕ) (x : ℕ) :
  (sum_T n x : ℚ) - (N_eq n : ℚ) =
    ∑ j ∈ range n,
      (3 : ℚ)^(n - 1 - j) *
        (2 : ℚ)^(2 * j) *
          ((2 : ℚ)^(S_prime j x) - 1) := by

  rw [sum_T, N_eq_as_sum]
  push_cast
  rw [← sum_sub_distrib]

  apply sum_congr rfl
  intro j hj

  rw [mul_sub, mul_one]
  congr 1

  have h_rel := s_relationship j x

  have h_exp_match :
      (2 : ℚ)^(S j x) =
        (2 : ℚ)^(2 * j) * (2 : ℚ)^(S_prime j x) := by
    rw [← zpow_natCast, h_rel, zpow_add₀ (by norm_num)]
    norm_cast

  rw [h_exp_match]
  ring

/--
The equilibrium state in perturbation language.
-/
def is_equilibrium (n : ℕ) (x : ℕ) : Prop :=
  ∀ i ∈ range n, delta x i = 0

/--
Equilibrium bridge.

The perturbation-language equilibrium is exactly the original valuation
condition used in Lemma 1A.
-/
lemma is_equilibrium_iff_all_val_two
  (n x : ℕ) :
  is_equilibrium n x ↔ ∀ k < n, val (T^[k] x) = 2 := by

  constructor

  · intro h_eq k hk

    have h_delta_zero :
        delta x k = 0 :=
      h_eq k (Finset.mem_range.mpr hk)

    unfold delta at h_delta_zero

    have h_cast :
        (val (T^[k] x) : ℤ) = 2 := by
      linarith

    exact_mod_cast h_cast

  · intro h_all k hk

    have h_val :
        val (T^[k] x) = 2 :=
      h_all k (Finset.mem_range.mp hk)

    unfold delta
    rw [h_val]
    norm_num

/--
The mixed perturbation state.
-/
def is_mixed_perturbation (n : ℕ) (x : ℕ) : Prop :=
  (∃ i ∈ range n, delta x i < 0) ∧
    (∃ j ∈ range n, 0 < delta x j)

/--
Exhaustive perturbation-space partition.

Every trajectory segment is exactly one of:
equilibrium, pure nonpositive with a negative term, pure nonnegative with a
positive term, or mixed.
-/
theorem perturbation_space_exhaustive (n x : ℕ) :
  is_equilibrium n x ∨
  ((∀ i ∈ range n, delta x i ≤ 0) ∧
    (∃ i ∈ range n, delta x i < 0)) ∨
  ((∀ i ∈ range n, 0 ≤ delta x i) ∧
    (∃ i ∈ range n, 0 < delta x i)) ∨
  is_mixed_perturbation n x := by

  by_cases h_neg : ∃ i ∈ range n, delta x i < 0

  · by_cases h_pos : ∃ j ∈ range n, 0 < delta x j

    · exact Or.inr (Or.inr (Or.inr ⟨h_neg, h_pos⟩))

    · have h_all_le :
        ∀ i ∈ range n, delta x i ≤ 0 := by
        intro i hi
        by_contra h_gt
        apply h_pos
        exact ⟨i, hi, by omega⟩

      exact Or.inr (Or.inl ⟨h_all_le, h_neg⟩)

  · by_cases h_pos : ∃ j ∈ range n, 0 < delta x j

    · have h_all_ge :
        ∀ i ∈ range n, 0 ≤ delta x i := by
        intro i hi
        by_contra h_lt
        apply h_neg
        exact ⟨i, hi, by omega⟩

      exact Or.inr (Or.inr (Or.inl ⟨h_all_ge, h_pos⟩))

    · have h_all_zero :
        ∀ i ∈ range n, delta x i = 0 := by
        intro i hi

        have h_not_lt : ¬ delta x i < 0 := by
          intro h
          apply h_neg
          exact ⟨i, hi, h⟩

        have h_not_gt : ¬ 0 < delta x i := by
          intro h
          apply h_pos
          exact ⟨i, hi, h⟩

        omega

      exact Or.inl h_all_zero

/--
Nontrivial cycle routing.

A nontrivial cycle cannot remain in equilibrium, so it must route into one of
the three perturbed branches.
-/
theorem non_trivial_cycle_routing (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn_pos : n > 0)
  (h_non_trivial : x > 1) :
  ((∀ i ∈ range n, delta x i ≤ 0) ∧
    (∃ i ∈ range n, delta x i < 0)) ∨
  ((∀ i ∈ range n, 0 ≤ delta x i) ∧
    (∃ i ∈ range n, 0 < delta x i)) ∨
  is_mixed_perturbation n x := by

  have h_exhaustive := perturbation_space_exhaustive n x

  have h_not_eq : ¬ is_equilibrium n x := by
    intro h_eq

    have h_all_two :
        ∀ k < n, val (T^[k] x) = 2 :=
      (is_equilibrium_iff_all_val_two n x).mp h_eq

    exact
      (non_trivial_cycle_forces_perturbation
        n x h_cycle hn_pos h_non_trivial)
      h_all_two

  rcases h_exhaustive with h_eq | h_pure_neg | h_pure_pos | h_mixed

  · exfalso
    exact h_not_eq h_eq

  · exact Or.inl h_pure_neg

  · exact Or.inr (Or.inl h_pure_pos)

  · exact Or.inr (Or.inr h_mixed)

end Section9_Perturbation_Model
-- ===============================================================
-- SECTION 10: NUMERATOR BOUNDS UNDER PERTURBATION
-- ===============================================================
section Section10_Numerator_Bounds

/--
Null Perturbation Identity.
Establishes that a sequence of zero prefix sums yields a numerator identical to the equilibrium baseline.
-/
theorem equality_case (n : ℕ) (x : ℕ) (h_zero : ∀ j ∈ range n, S_prime j x = 0) :
  (sum_T n x : ℚ) = (N_eq n : ℚ) := by
  have h_diff := exact_difference_formula n x
  have h_rhs_zero : ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime j x) - 1) = 0 := by
    apply sum_eq_zero
    intro j hj
    rw [h_zero j hj, zpow_zero, sub_self, mul_zero]
  rw [h_rhs_zero] at h_diff
  exact sub_eq_zero.mp h_diff

/--
Upper Bound for Non-Positive Trajectories.
Demonstrates that a non-positive prefix sequence restricts the total numerator to the equilibrium baseline or below.
-/
theorem monotone_nonpositive_case (n : ℕ) (x : ℕ) (h_neg : ∀ j ∈ range n, S_prime j x ≤ 0) :
  (sum_T n x : ℚ) ≤ (N_eq n : ℚ) := by
  have h_diff := exact_difference_formula n x
  rw [← sub_nonpos, h_diff]
  
  apply sum_nonpos
  intro j hj
  
  have h_weight_pos : (0 : ℚ) < (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by
    apply mul_pos <;> apply pow_pos <;> norm_num
    
  have h_term_nonpos : (2 : ℚ)^(S_prime j x) - 1 ≤ 0 := by
    rw [sub_nonpos]
    apply zpow_le_one_of_nonpos₀
    · norm_num
    · exact h_neg j hj
    
  exact mul_nonpos_of_nonneg_of_nonpos h_weight_pos.le h_term_nonpos

/--
Lower Bound for Non-Negative Trajectories.
Demonstrates that a non-negative prefix sequence forces the total numerator to meet or exceed the equilibrium baseline.
-/
theorem monotone_nonnegative_case (n : ℕ) (x : ℕ) (h_pos : ∀ j ∈ range n, 0 ≤ S_prime j x) :
  (N_eq n : ℚ) ≤ (sum_T n x : ℚ) := by
  have h_diff := exact_difference_formula n x
  
  rw [← sub_nonneg]
  rw [h_diff]
  
  apply sum_nonneg
  intro j hj
  
  have h_weight_pos : (0 : ℚ) < (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by
    apply mul_pos <;> apply pow_pos <;> norm_num
    
  have h_term_nonneg : 0 ≤ (2 : ℚ)^(S_prime j x) - 1 := by
    rw [le_sub_iff_add_le, zero_add]
    apply one_le_zpow₀
    · norm_num
    · exact h_pos j hj
    
  exact mul_nonneg h_weight_pos.le h_term_nonneg

end Section10_Numerator_Bounds

#print axioms equality_case
#print axioms monotone_nonpositive_case
#print axioms monotone_nonnegative_case
#check equality_case
#check monotone_nonpositive_case
#check monotone_nonnegative_case

-- ===============================================================
-- SECTION 11: PRELIMINARY BOUNDS & INTEGER LIFTS
-- ===============================================================
section Section11_Valuation_Target

/--
Logarithmic Monotonicity for the Collatz Bound.
Converts the integer threshold 3^n < 2^S into a real logarithmic inequality.
-/
lemma log_ratio_bound (n S_val : ℕ) (hn : 0 < n) (h_bound : 3^n < 2^S_val) :
  Real.log 3 / Real.log 2 < (S_val : ℝ) / (n : ℝ) := by
  
  have h_bound_real : (3 : ℝ)^n < (2 : ℝ)^S_val := by exact_mod_cast h_bound
  
  have h_log_lt : Real.log ((3 : ℝ)^n) < Real.log ((2 : ℝ)^S_val) := by
    apply Real.log_lt_log
    · positivity
    · exact h_bound_real
    
  rw [Real.log_pow, Real.log_pow] at h_log_lt
  
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog2_pos : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
    
  have hn_inv_pos : 0 < (n : ℝ)⁻¹ := inv_pos.mpr hn_pos
  have h_div1 : ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ < ((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹ := by
    exact mul_lt_mul_of_pos_right h_log_lt hn_inv_pos
    
  have h_cancel_n : ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ = Real.log 3 := by
    calc ((n : ℝ) * Real.log 3) * (n : ℝ)⁻¹ 
      _ = Real.log 3 * ((n : ℝ) * (n : ℝ)⁻¹) := by ring
      _ = Real.log 3 * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hn_pos)]
      _ = Real.log 3 := by ring
      
  rw [h_cancel_n] at h_div1
  
  have hlog2_inv_pos : 0 < (Real.log 2)⁻¹ := inv_pos.mpr hlog2_pos
  have h_div2 : Real.log 3 * (Real.log 2)⁻¹ < (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹ := by
    exact mul_lt_mul_of_pos_right h_div1 hlog2_inv_pos
    
  have h_rhs_simp : (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹ = (S_val : ℝ) / (n : ℝ) := by
    calc (((S_val : ℝ) * Real.log 2) * (n : ℝ)⁻¹) * (Real.log 2)⁻¹
      _ = (S_val : ℝ) * (n : ℝ)⁻¹ * (Real.log 2 * (Real.log 2)⁻¹) := by ring
      _ = (S_val : ℝ) * (n : ℝ)⁻¹ * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hlog2_pos)]
      _ = (S_val : ℝ) / (n : ℝ) := by ring
      
  have h_lhs_simp : Real.log 3 * (Real.log 2)⁻¹ = Real.log 3 / Real.log 2 := by ring
  
  rw [h_lhs_simp, h_rhs_simp] at h_div2
  exact h_div2

/--
Constraint 5: The Negative Deficit Bound.
Given S = 2n - p, proves that the number of negative perturbations (p) 
is bounded linearly by n: p/n < 2 - (log_3 / log_2).
-/
theorem constraint_5_deficit_bound (n S_val p : ℕ) 
  (hn : 0 < n) 
  (h_bound : 3^n < 2^S_val)
  (h_deficit : S_val + p = 2 * n) :
  (p : ℝ) / (n : ℝ) < 2 - (Real.log 3 / Real.log 2) := by
  
  have h_ratio := log_ratio_bound n S_val hn h_bound
  
  have h_S_eq : (S_val : ℝ) = 2 * (n : ℝ) - (p : ℝ) := by
    have h_cast : (S_val : ℝ) + (p : ℝ) = 2 * (n : ℝ) := by exact_mod_cast h_deficit
    linarith
    
  rw [h_S_eq] at h_ratio
  
  have hn_pos : (n : ℝ) ≠ 0 := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
    
  have h_distrib : (2 * (n : ℝ) - (p : ℝ)) / (n : ℝ) = 2 - (p : ℝ) / (n : ℝ) := by
    calc (2 * (n : ℝ) - (p : ℝ)) / (n : ℝ) 
      _ = (2 * (n : ℝ)) / (n : ℝ) - (p : ℝ) / (n : ℝ) := by rw [sub_div]
      _ = 2 * ((n : ℝ) / (n : ℝ)) - (p : ℝ) / (n : ℝ) := by ring
      _ = 2 * 1 - (p : ℝ) / (n : ℝ) := by rw [div_self hn_pos]
      _ = 2 - (p : ℝ) / (n : ℝ) := by ring
      
  rw [h_distrib] at h_ratio
  linarith

/--
Integer Field Diophantine Lift.
Maps the core Diophantine equation and its variable representations into the integer ring (ℤ).
-/
lemma cycle_diophantine_int (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := by
  
  have h_eq := cycle_implies_explicit_diophantine n x h_cycle
  have h_threshold : 3^n ≤ 2^(S n x) := le_of_lt (cycle_existence_threshold n x h_cycle hn)
  
  have h_cast : ((sum_T n x : ℤ)) = (((2^(S n x) - 3^n) * x : ℕ) : ℤ) := by rw [h_eq]
  rw [h_cast]
  
  rw [Nat.cast_mul, Nat.cast_sub h_threshold]
  push_cast
  ring

/--
Integer Formulation of Equilibrium Numerator.
Establishes (N_eq : ℤ) = 2^(2n) - 3^n to facilitate algebraic comparisons.
-/
lemma N_eq_int (n : ℕ) : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := by
  unfold N_eq
  have h_pow : 3^n ≤ 4^n := Nat.pow_le_pow_left (by norm_num) n
  rw [Nat.cast_sub h_pow]
  push_cast
  have h_4 : (4 : ℤ) = 2^2 := by norm_num
  rw [h_4, ← pow_mul]

end Section11_Valuation_Target

#print axioms constraint_5_deficit_bound
#check log_ratio_bound
#check constraint_5_deficit_bound
#check cycle_diophantine_int
-- ===============================================================
-- SECTION 12: LEMMA 1C SETUP (Pure Negative Definition)
-- ===============================================================
section Section12_Lemma1C_Setup

/--
Pure Negative Perturbation Definition.
-/
def is_pure_negative (n : ℕ) (x : ℕ) : Prop :=
  (∀ i ∈ range n, delta x i ≤ 0) ∧ (S_prime n x < 0)

/--
Global Exponent Sum Upper Bound.
-/
theorem pure_negative_S_lt_2n (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) : 
  S n x < 2 * n := by
  
  have h_rel := s_relationship n x
  have h_prime_neg : S_prime n x < 0 := h_neg.2
  
  zify at h_rel ⊢
  rw [h_rel]
  linarith

end Section12_Lemma1C_Setup

#print axioms pure_negative_S_lt_2n
#check pure_negative_S_lt_2n
-- ===============================================================
-- SECTION 13: LEMMA 1C (PURE NEGATIVE PERTURBATION CONSEQUENCE)
-- ===============================================================
section Section13_Lemma1C_Pure_Negative_Perturbation

/--
Partial Sum Upper Bound.
Demonstrates that the cumulative sum of remaining exponents from index j to n 
is bounded by twice the step count.
-/
theorem pure_negative_partial_sum_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) (j : ℕ) (hj : j ≤ n) :
  S n x - S j x ≤ 2 * (n - j) := by
  
  rw [Nat.sub_le_iff_le_add]

  suffices h_gen : ∀ k, j + k ≤ n → S (j + k) x ≤ S j x + 2 * k by
    specialize h_gen (n - j)
    rw [Nat.add_sub_of_le hj] at h_gen
    rw [add_comm]
    exact h_gen (Nat.le_refl n)

  intro k hk_le
  induction k with
  | zero =>
    simp
  | succ k ih =>
    rw [Nat.add_succ, S]
    rw [Nat.mul_succ]      
    rw [← add_assoc]       
    
    apply Nat.add_le_add
    · apply ih
      exact Nat.le_of_succ_le hk_le
    · have h_idx : j + k < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hk_le
      have h_delta := h_neg.1 (j + k) (Finset.mem_range.mpr h_idx)
      dsimp [delta] at h_delta
      zify at h_delta ⊢
      linarith
#check pure_negative_partial_sum_bound
/--
Term-wise Geometric Lower Bound.
Formulates the minimum algebraic value for individual terms within the perturbed summation.
-/
theorem pure_negative_term_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) (j : ℕ) (hj : j ∈ range n) :
  (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) ≥ 
  ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) := by

  let k := n - 1 - j
  have hj_lt : j < n := Finset.mem_range.mp hj 
  have hk_rel : n - j = k + 1 := by omega
  
  have h_idx_le : j ≤ n := Nat.le_of_lt hj_lt
  have h_exp_bound := pure_negative_partial_sum_bound n x h_neg j h_idx_le
  
  have h_exp_bound2 : S n x - S j x ≤ 2 * (k + 1) := by
    rw [hk_rel] at h_exp_bound
    exact h_exp_bound

  have h_exp_add : S n x ≤ S j x + 2 * (k + 1) := by omega

  have h_pow_nat : 2 ^ S n x ≤ 2 ^ (S j x + 2 * (k + 1)) := 
    Nat.pow_le_pow_right (by norm_num) h_exp_add

  have h_pow_simp : 2 ^ (S j x + 2 * (k + 1)) = 2 ^ S j x * 4 ^ (k + 1) := by
    rw [pow_add, pow_mul]
    rfl

  rw [h_pow_simp] at h_pow_nat

  have h_pow_rat : (2 : ℚ) ^ S n x ≤ (2 : ℚ) ^ S j x * (4 : ℚ) ^ (k + 1) := by
    exact_mod_cast h_pow_nat

  have h_div : (2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1) ≤ (2 : ℚ) ^ S j x := by
    rw [div_le_iff₀]
    · linarith
    · positivity

  have h_mul : ((2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1)) * (3 : ℚ) ^ k ≤ 
               (2 : ℚ) ^ S j x * (3 : ℚ) ^ k := by
    apply mul_le_mul_of_nonneg_right h_div
    positivity

  change ((2 : ℚ) ^ S n x / 4) * (3 / 4 : ℚ) ^ k ≤ (3 : ℚ) ^ k * (2 : ℚ) ^ S j x

  have h_goal_lhs : ((2 : ℚ) ^ S n x / 4) * (3 / 4 : ℚ) ^ k = 
                    ((2 : ℚ) ^ S n x / (4 : ℚ) ^ (k + 1)) * (3 : ℚ) ^ k := by
    rw [div_pow, pow_succ]
    ring

  have h_goal_rhs : (3 : ℚ) ^ k * (2 : ℚ) ^ S j x = 
                    (2 : ℚ) ^ S j x * (3 : ℚ) ^ k := by
    ring

  rw [h_goal_lhs, h_goal_rhs]
  exact h_mul
#check pure_negative_term_bound
/--
Geometric Summation Lower Bound.
Establishes the absolute lower bound for the total perturbed numerator.
-/
theorem pure_negative_numerator_lower_bound (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) :
  (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) ≤ (sum_T n x : ℚ) := by
  
  have h_sum_T_cast : (sum_T n x : ℚ) = ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) := by
    rw [sum_T]
    push_cast
    rfl
  
  rw [h_sum_T_cast]
  
  have h_sum_le : ∑ j ∈ range n, ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) ≤ 
                  ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(S j x) := by
    apply sum_le_sum
    intro j hj
    exact pure_negative_term_bound n x h_neg j hj

  have h_factor : ∑ j ∈ range n, ((2 : ℚ)^(S n x) / 4) * (3 / 4 : ℚ)^(n - 1 - j) = 
                  ((2 : ℚ)^(S n x) / 4) * ∑ j ∈ range n, (3 / 4 : ℚ)^(n - 1 - j) := by
    rw [mul_sum]

  have h_reindex : ∑ j ∈ range n, (3 / 4 : ℚ)^(n - 1 - j) = ∑ k ∈ range n, (3 / 4 : ℚ)^k := by
    exact sum_range_reflect (fun k => (3 / 4 : ℚ)^k) n

  have h_geom_sum : ∑ k ∈ range n, (3 / 4 : ℚ)^k = (1 - (3 / 4 : ℚ)^n) / (1 - 3 / 4) := by
    have h_standard := geom_sum_eq (x := (3 / 4 : ℚ)) (by norm_num) n
    rw [h_standard]
    generalize (3 / 4 : ℚ)^n = B
    ring

  have h_alg_eq : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) = 
        ((2 : ℚ)^(S n x) / 4) * ((1 - (3 / 4 : ℚ)^n) / (1 - 3 / 4)) := by
    generalize (2 : ℚ)^(S n x) = A
    generalize (3 / 4 : ℚ)^n = B
    ring

  rw [h_alg_eq, ← h_geom_sum, ← h_reindex, ← h_factor]
  exact h_sum_le
#check pure_negative_numerator_lower_bound
/--
Lemma 1C: Pure Negative Inequality.
Demonstrates that a purely negative perturbation forces the numerator to exceed the denominator.
-/
theorem pure_negative_numerator_gt_denominator (n : ℕ) (x : ℕ) 
  (h_neg : is_pure_negative n x) :
  ((2 : ℚ)^(S n x) - (3 : ℚ)^n) < (sum_T n x : ℚ) := by
  
  have h_lower := pure_negative_numerator_lower_bound n x h_neg
  have h_S_lt : S n x < 2 * n := pure_negative_S_lt_2n n x h_neg
  
  have h_p_ex : ∃ p : ℕ, S n x + p = 2 * n ∧ p ≥ 1 := by
    use (2 * n - S n x)
    omega
  rcases h_p_ex with ⟨p, h_Sp, hp⟩

  have h_four : (4 : ℚ)^n = (2 : ℚ)^(2 * n) := by
    have : (4 : ℚ) = 2^2 := by norm_num
    rw [this, ← pow_mul]
    
  have h_pow2_add : (2 : ℚ)^(2 * n) = (2 : ℚ)^(S n x) * (2 : ℚ)^p := by
    rw [← h_Sp, pow_add]
    
  have h_subst : (4 : ℚ)^n = (2 : ℚ)^(S n x) * (2 : ℚ)^p := by
    rw [h_four, h_pow2_add]

  have h_frac : (3 / 4 : ℚ)^n = (3 : ℚ)^n / ((2 : ℚ)^(S n x) * (2 : ℚ)^p) := by
    rw [div_pow, h_subst]

  have h2S : (2 : ℚ)^(S n x) ≠ 0 := by positivity

  have h_alg_diff : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) = 
                    (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := by
    calc (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n)
      _ = (2 : ℚ)^(S n x) - (2 : ℚ)^(S n x) * (3 / 4 : ℚ)^n - (2 : ℚ)^(S n x) + (3 : ℚ)^n := by ring
      _ = (3 : ℚ)^n - (2 : ℚ)^(S n x) * ((3 : ℚ)^n / ((2 : ℚ)^(S n x) * (2 : ℚ)^p)) := by
          rw [h_frac]
          ring
      _ = (3 : ℚ)^n - ((2 : ℚ)^(S n x) * (3 : ℚ)^n) / ((2 : ℚ)^(S n x) * (2 : ℚ)^p) := by
          congr 1
          rw [mul_div_assoc']
      _ = (3 : ℚ)^n - (((2 : ℚ)^(S n x) * (3 : ℚ)^n) / (2 : ℚ)^(S n x)) / (2 : ℚ)^p := by
          rw [div_mul_eq_div_div]
      _ = (3 : ℚ)^n - (3 : ℚ)^n / (2 : ℚ)^p := by
          congr 2
          exact mul_div_cancel_left₀ ((3 : ℚ)^n) h2S
      _ = (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := by ring

  have hp_pow : (2 : ℚ)^1 ≤ (2 : ℚ)^p := by 
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hp)
    
  have hp_inv : 1 / (2 : ℚ)^p ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith

  have h_factor : 0 < 1 - 1 / (2 : ℚ)^p := by linarith
  have h_3_pos : (0 : ℚ) < (3 : ℚ)^n := by positivity
  
  have h_diff_pos : 0 < (3 : ℚ)^n * (1 - 1 / (2 : ℚ)^p) := mul_pos h_3_pos h_factor

  have h_N_sub_D : (2 : ℚ)^(S n x) * (1 - (3 / 4 : ℚ)^n) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) ≤ 
                   (sum_T n x : ℚ) - ((2 : ℚ)^(S n x) - (3 : ℚ)^n) := by linarith
                   
  rw [h_alg_diff] at h_N_sub_D
  linarith

end Section13_Lemma1C_Pure_Negative_Perturbation
#check pure_negative_numerator_gt_denominator
#print axioms pure_negative_term_bound
#print axioms pure_negative_numerator_lower_bound
#print axioms pure_negative_numerator_gt_denominator
-------------------------------------------------------------------------------------------
-- ===============================================================
-- CONSTRAINT 3: NONTRIVIAL CYCLE RATIO LOWER BOUND
-- ===============================================================

/--
Constraint 3, powers of two are not divisible by three.
-/
lemma constraint_3_three_not_dvd_two_pow
  (m : ℕ) :
  ¬ 3 ∣ 2^m := by

  intro h

  cases m with
  | zero =>
      norm_num at h

  | succ m =>
      have h_prime : Nat.Prime 3 := by
        norm_num

      have h_three_dvd_two :
          3 ∣ 2 := by
        exact h_prime.dvd_of_dvd_pow h

      norm_num at h_three_dvd_two

/--
Constraint 3, integer form.

The integer power `(2 : ℤ)^m` is not divisible by `(3 : ℤ)`.
-/
lemma constraint_3_three_not_dvd_two_pow_int
  (m : ℕ) :
  ¬ (3 : ℤ) ∣ (2 : ℤ)^m := by

  intro h

  have h_nat :
      3 ∣ 2^m := by
    exact_mod_cast h

  exact constraint_3_three_not_dvd_two_pow m h_nat

/--
Constraint 3, numerator is coprime to three.

For `0 < n`, the recursive numerator is never divisible by `3`, because

`Z_{k+1} = 3 Z_k + 2^(S_k)`

and the final summand is a power of two.
-/
lemma constraint_3_closed_numerator_not_three_dvd
  (n x : ℕ)
  (hn : 0 < n) :
  ¬ 3 ∣ closed_numerator n x := by

  cases n with
  | zero =>
      omega

  | succ k =>
      intro h

      unfold closed_numerator at h

      have h_int :
          (3 : ℤ) ∣
            (3 : ℤ) * (closed_numerator k x : ℤ) +
              (2 : ℤ)^(S k x) := by
        exact_mod_cast h

      have h_three_part :
          (3 : ℤ) ∣
            (3 : ℤ) * (closed_numerator k x : ℤ) := by
        exact dvd_mul_right 3 (closed_numerator k x : ℤ)

      have h_pow_part :
          (3 : ℤ) ∣ (2 : ℤ)^(S k x) := by
        have h_sub :
            (3 : ℤ) ∣
              ((3 : ℤ) * (closed_numerator k x : ℤ) +
                  (2 : ℤ)^(S k x)) -
                (3 : ℤ) * (closed_numerator k x : ℤ) :=
          dvd_sub h_int h_three_part

        have h_simp :
            ((3 : ℤ) * (closed_numerator k x : ℤ) +
                (2 : ℤ)^(S k x)) -
              (3 : ℤ) * (closed_numerator k x : ℤ)
              =
            (2 : ℤ)^(S k x) := by
          ring

        rwa [h_simp] at h_sub

      exact
        constraint_3_three_not_dvd_two_pow_int
          (S k x)
          h_pow_part

/--
Constraint 3, `sum_T` numerator is not divisible by three.

This transfers the recursive numerator statement to the closed summation
numerator using `closed_numerator_eq_sum_T`.
-/
lemma constraint_3_sum_T_not_three_dvd
  (n x : ℕ)
  (hn : 0 < n) :
  ¬ 3 ∣ sum_T n x := by

  intro h

  have h_closed :
      closed_numerator n x = sum_T n x :=
    closed_numerator_eq_sum_T n x

  rw [← h_closed] at h

  exact constraint_3_closed_numerator_not_three_dvd n x hn h

/--
Constraint 3, the cycle ratio is not divisible by three.

If `3 ∣ x`, then the cycle equation

`D_new * x = N_new`

would force `3 ∣ N_new`, contradicting the previous numerator result.
-/
lemma constraint_3_cycle_ratio_not_three_dvd
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n) :
  ¬ 3 ∣ x := by

  intro h_three_x

  have h_sum_not :
      ¬ 3 ∣ sum_T n x :=
    constraint_3_sum_T_not_three_dvd n x hn

  have h_cycle_eq :
      (2^(S n x) - 3^n) * x = sum_T n x :=
    cycle_implies_explicit_diophantine n x h_cycle

  have h_sum_dvd :
      3 ∣ sum_T n x := by
    rw [← h_cycle_eq]
    exact dvd_mul_of_dvd_right h_three_x (2^(S n x) - 3^n)

  exact h_sum_not h_sum_dvd

/--
Constraint 3, nontrivial cycle ratio lower bound.

A nontrivial cycle ratio is odd, greater than `1`, and not divisible by `3`.
Therefore it cannot be `2`, `3`, or `4`, so it must satisfy `5 ≤ x`.
-/
theorem constraint_3_nontrivial_cycle_ratio_ge_five
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1) :
  5 ≤ x := by

  have h_odd :
      x % 2 = 1 :=
    cycle_implies_odd n x h_cycle hn

  have h_not_three :
      ¬ 3 ∣ x :=
    constraint_3_cycle_ratio_not_three_dvd n x h_cycle hn

  by_contra h_not

  have hx_le_four :
      x ≤ 4 := by
    omega

  interval_cases x

  · simp at h_odd

  · exact h_not_three (by norm_num)

  · simp at h_odd

#check constraint_3_three_not_dvd_two_pow
#check constraint_3_three_not_dvd_two_pow_int
#check constraint_3_closed_numerator_not_three_dvd
#check constraint_3_sum_T_not_three_dvd
#check constraint_3_cycle_ratio_not_three_dvd
#check constraint_3_nontrivial_cycle_ratio_ge_five
-- ===============================================================
-- SECTION 14: LEMMA 1D (Pure Positive Impossibility Bounds)
-- ===============================================================
section Section14_Lemma1D_Pure_Positive_Perturbation

/--
Pure Positive Perturbation Definition.
Defines a purely positive trajectory where all local perturbations are non-negative 
and the cumulative perturbation is positive.
-/
def is_pure_positive (n : ℕ) (x : ℕ) : Prop :=
  (∀ i ∈ range n, 0 ≤ delta x i) ∧ (0 < S_prime n x)

/--
Global Exponent Sum Lower Bound.
Demonstrates that a purely positive perturbation forces the global exponent sum 
above the 2n baseline.
-/
theorem pure_positive_S_gt_2n (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) : 
  2 * n < S n x := by
  
  have h_rel := s_relationship n x
  have h_prime_pos : 0 < S_prime n x := h_pos.2
  
  zify at h_rel ⊢
  rw [h_rel]
  linarith

noncomputable def D_new (n : ℕ) (x : ℕ) : ℚ := (2 : ℚ)^(S n x) - (3 : ℚ)^n
noncomputable def Delta_D (n : ℕ) (x : ℕ) : ℚ := D_new n x - (D_eq n : ℚ)
noncomputable def Delta_N (n : ℕ) (x : ℕ) : ℚ := (sum_T n x : ℚ) - (N_eq n : ℚ)
#check pure_positive_S_gt_2n
/--
Exact Denominator Deviation.
Formulates the precise algebraic change in the denominator relative to the equilibrium baseline.
-/
theorem exact_delta_D (n : ℕ) (x : ℕ) :
  Delta_D n x = (2 : ℚ)^(2 * n) * ((2 : ℚ)^(S_prime n x) - 1) := by
  dsimp [Delta_D, D_new, D_eq]
  
  have h_le : 3^n ≤ 2^(2 * n) := by
    rw [pow_mul, show 2^2 = 4 by rfl]
    exact Nat.pow_le_pow_left (by norm_num) n
    
  rw [Nat.cast_sub h_le]
  push_cast
  
  have h_cancel : ((2 : ℚ)^(S n x) - (3 : ℚ)^n) - ((2 : ℚ)^(2 * n) - (3 : ℚ)^n) = 
                  (2 : ℚ)^(S n x) - (2 : ℚ)^(2 * n) := by ring
  rw [h_cancel]
  
  have h_rel := s_relationship n x
  
  have h_exp_match : (2 : ℚ)^(S n x) = (2 : ℚ)^(2 * n) * (2 : ℚ)^(S_prime n x) := by
    rw [← zpow_natCast, h_rel, zpow_add₀ (by norm_num)]
    norm_cast
    
  rw [h_exp_match]
  ring
#check exact_delta_D
----------------------------------------------------------------------
theorem pure_positive_prefix_mono (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) (j : ℕ) (hj : j ≤ n) :
  S_prime j x ≤ S_prime n x := by
  dsimp [S_prime]
  
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i hi _
    exact h_pos.1 i hi
#check pure_positive_prefix_mono
/--
Factor Monotonicity.
-/
theorem pure_positive_factor_mono (n : ℕ) (x : ℕ) 
  (h_pos : is_pure_positive n x) (j : ℕ) (hj : j ≤ n) :
  (2 : ℚ)^(S_prime j x) - 1 ≤ (2 : ℚ)^(S_prime n x) - 1 := by
  
  have h_mono := pure_positive_prefix_mono n x h_pos j hj
  
  have h_pow_le : (2 : ℚ)^(S_prime j x) ≤ (2 : ℚ)^(S_prime n x) := by
    apply zpow_le_zpow_right₀ (by norm_num) h_mono
    
  linarith
#check pure_positive_factor_mono
/--
Numerator Deviation Upper Bound.
Establishes the maximum possible algebraic growth for the numerator.
-/
theorem delta_N_upper_bound (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) :
  Delta_N n x ≤ ((2 : ℚ)^(S_prime n x) - 1) * (N_eq n : ℚ) := by
  
  rw [Delta_N, exact_difference_formula]
  
  have h_sum_le : ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime j x) - 1) ≤ 
                  ∑ j ∈ range n, (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) * ((2 : ℚ)^(S_prime n x) - 1) := by
    apply sum_le_sum
    intro j hj
    have h_weight_pos : 0 ≤ (3 : ℚ)^(n - 1 - j) * (2 : ℚ)^(2 * j) := by positivity
    apply mul_le_mul_of_nonneg_left _ h_weight_pos
    exact pure_positive_factor_mono n x h_pos j (Nat.le_of_lt (Finset.mem_range.mp hj))

  rw [← sum_mul] at h_sum_le
  rw [mul_comm] at h_sum_le
  rw [← N_eq_as_sum] at h_sum_le
  
  exact h_sum_le
#check delta_N_upper_bound
/--
Rational Transformation of the Equilibrium Numerator.
Maps the equilibrium numerator definition to the rational field.
-/
theorem N_eq_rational (n : ℕ) : 
  (N_eq n : ℚ) = (2 : ℚ)^(2 * n) - (3 : ℚ)^n := by
  dsimp [N_eq]
  rw [pow_mul, show (2 : ℚ)^2 = 4 by rfl]
  rw [Nat.cast_sub]
  · rw [Nat.cast_pow, Nat.cast_pow]
    rfl
  · exact Nat.pow_le_pow_left (by norm_num) n
#check N_eq_rational
/--
Equilibrium Numerator Upper Bound.
Demonstrates that the equilibrium numerator is bounded above by 2^(2n).
-/
theorem N_eq_lt_2pow2n (n : ℕ) : 
  (N_eq n : ℚ) < (2 : ℚ)^(2 * n) := by
  rw [N_eq_rational]
  have h_pos : 0 < (3 : ℚ)^n := by positivity
  linarith
#check N_eq_lt_2pow2n
/--
Growth Factor Positivity.
Demonstrates that a positive cumulative perturbation yields an exponential factor greater than 1.
-/
theorem h_factor_pos_isolated (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) : 
  (1 : ℚ) < (2 : ℚ)^(S_prime n x) := by
  have h_S_pos : 0 < S_prime n x := by
    have h_ge_one : 1 ≤ S_prime n x := h_pos.2
    linarith
  apply one_lt_zpow₀
  · exact one_lt_two
  · exact h_S_pos
#check h_factor_pos_isolated
/--
Lemma 1D: Pure Positive Comparison Theorem.
Proves that a purely positive perturbation causes the denominator to exceed the numerator, 
preventing an integer cycle ratio.
-/
theorem Lemma_1D_Final_Comparison (n : ℕ) (x : ℕ) (h_pos : is_pure_positive n x) :
  (sum_T n x : ℚ) < (2 : ℚ)^(S n x) - (3 : ℚ)^n := by
  
  let factor := (2 : ℚ)^(S_prime n x) - 1
  have h_f_pos : 0 < factor := by
    apply sub_pos.mpr
    exact h_factor_pos_isolated n x h_pos
    
  have h_delta_comp : Delta_N n x < Delta_D n x := by
    rw [exact_delta_D n x]
    calc Delta_N n x 
      _ ≤ factor * (N_eq n : ℚ) := delta_N_upper_bound n x h_pos
      _ < factor * (2 : ℚ)^(2 * n) := mul_lt_mul_of_pos_left (N_eq_lt_2pow2n n) h_f_pos
      _ = (2 : ℚ)^(2 * n) * factor := by rw [mul_comm]

  unfold Delta_N Delta_D D_new at h_delta_comp
  
  have h_nats_eq : N_eq n = D_eq n := by
    unfold N_eq D_eq
    rw [pow_mul]
    have h_base : 2^2 = 4 := by rfl
    rw [h_base]
  
  have h_const_eq : (N_eq n : ℚ) = (D_eq n : ℚ) := 
    congrArg (fun (k : ℕ) => (k : ℚ)) h_nats_eq

  rw [h_const_eq] at h_delta_comp
  linarith

end Section14_Lemma1D_Pure_Positive_Perturbation
#check Lemma_1D_Final_Comparison
#print axioms exact_delta_D
#print axioms delta_N_upper_bound
#print axioms Lemma_1D_Final_Comparison
---------------------------------------------------------------------------------------
section Section15_Lemma2D_Definitions

/--
The Actual Numerator Deviation (Net Increment Form).
Translates the manuscript's summation bounds (k=2 to n) to the zero-indexed equivalent (j=1 to n-1).
Manuscript form: \sum_{k=2}^n 3^{n-k}(2^{S_{k-1}} - 2^{2k-2})
Lean 4 form: \sum_{j \in Ico 1 n} 3^{n-1-j} * (2^{S_j} - 2^{2j})
-/
noncomputable def delta_N_actual_inc (n x : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 n, (3 : ℤ)^(n - 1 - j) * ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j))

/--
The Actual Numerator Deviation (Net Decrement Form).
Translates the net decrement summation bounds equivalently.
Manuscript form: \sum_{k=2}^n 3^{n-k}(2^{2k-2} - 2^{S_{k-1}})
Lean 4 form: \sum_{j \in Ico 1 n} 3^{n-1-j} * (2^{2j} - 2^{S_j})
-/
noncomputable def delta_N_actual_dec (n x : ℕ) : ℤ :=
  ∑ j ∈ Ico 1 n, (3 : ℤ)^(n - 1 - j) * ((2 : ℤ)^(2 * j) - (2 : ℤ)^(S j x))

end Section15_Lemma2D_Definitions

section Section15_Lemma2D_Step_1_Derivation

/--
Derivation of the Cycle Condition for Net Decrement.
-/
theorem lemma_2D_decrement_stepwise (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (N_eq n : ℤ) - (sum_T n x : ℤ) = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n := by
  
  -- Establishes the fundamental cycle equation Z * D_new = N_new

  have step_a : (sum_T n x : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    calc (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := cycle_diophantine_int n x h_cycle hn
      _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by ring

  -- Isolates the actual numerator deviation ΔN = N_eq - N_new

  have step_c : (N_eq n : ℤ) - (sum_T n x : ℤ) = (N_eq n : ℤ) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    rw [step_a]

  -- Substitutes the expanded formulas for the equilibrium numerator and perturbed denominator
  have h_N_eq : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := N_eq_int n
  have step_d : (N_eq n : ℤ) - (sum_T n x : ℤ) = ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    rw [step_c, h_N_eq]

  -- Expands and groups the algebraic terms to form the final bifurcated expression
  calc (N_eq n : ℤ) - (sum_T n x : ℤ)
    _ = ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) - (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := step_d
    _ = (2 : ℤ)^(2 * n) - (3 : ℤ)^n - (x : ℤ) * (2 : ℤ)^(S n x) + (x : ℤ) * (3 : ℤ)^n := by ring
    _ = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) * (3 : ℤ)^n - (3 : ℤ)^n) := by ring
    _ = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n := by ring

end Section15_Lemma2D_Step_1_Derivation
section Lemma_2D_Step_2_Derivation
#check lemma_2D_decrement_stepwise
/--
Derivation of the Cycle Condition for Net Increment.
-/
theorem lemma_2D_increment_stepwise (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) :
  (sum_T n x : ℤ) - (N_eq n : ℤ) = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + (1 - (x : ℤ)) * (3 : ℤ)^n := by

  have h_cycle_cond : (sum_T n x : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by
    calc (sum_T n x : ℤ) = (2 : ℤ)^(S n x) * (x : ℤ) - (3 : ℤ)^n * (x : ℤ) := cycle_diophantine_int n x h_cycle hn
      _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) := by ring

  -- Formulates the deviation identity N_new = ΔN + N_eq and substitute the components
  have h_N_eq : (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n := N_eq_int n
  
  have step_b : (sum_T n x : ℤ) - (N_eq n : ℤ) = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) - (N_eq n : ℤ) := by
    rw [h_cycle_cond]

  calc (sum_T n x : ℤ) - (N_eq n : ℤ)
    _ = (x : ℤ) * ((2 : ℤ)^(S n x) - (3 : ℤ)^n) - ((2 : ℤ)^(2 * n) - (3 : ℤ)^n) := by rw [step_b, h_N_eq]
    _ = (x : ℤ) * (2 : ℤ)^(S n x) - (x : ℤ) * (3 : ℤ)^n - (2 : ℤ)^(2 * n) + (3 : ℤ)^n := by ring
    _ = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + ((3 : ℤ)^n - (x : ℤ) * (3 : ℤ)^n) := by ring
    _ = ((x : ℤ) * (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) + (1 - (x : ℤ)) * (3 : ℤ)^n := by ring

end Lemma_2D_Step_2_Derivation
#print axioms lemma_2D_decrement_stepwise
#print axioms lemma_2D_increment_stepwise
#check lemma_2D_increment_stepwise
-- ===============================================================
-- SECTION 16: Lemma 2D Corollary (3-Adic Valuation Alignment)
-- ===============================================================

/--
3-Adic Valuation Alignment Requirement.
Proves that a non-trivial cycle is impossible if the 3-adic 
valuation of the LHS and RHS of the cycle equation (derived in Lemma 2D) 
do not perfectly align.
-/
theorem cycle_impossible_if_valuation_mismatch (n x : ℕ) 
  (h_cycle : is_cycle n x) (hn : 0 < n)
  (LHS RHS : ℤ)

  (h_LHS : LHS = (N_eq n : ℤ) - (sum_T n x : ℤ))
  (h_RHS : RHS = ((2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)) + ((x : ℤ) - 1) * (3 : ℤ)^n)
  
  -- The Mismatch Condition: The 3-adic valuations are not equal
  (h_val_mismatch : padicValNat 3 LHS.natAbs ≠ padicValNat 3 RHS.natAbs) :
  False := by
  
  -- Step 1: Invoke Lemma 2D to establish the mathematical equality of the two sides
  have h_2D := lemma_2D_decrement_stepwise n x h_cycle hn
  
  -- Step 2: Substitute the local LHS and RHS definitions to form the identity LHS = RHS
  have h_eq : LHS = RHS := by
    rw [h_LHS, h_RHS]
    exact h_2D
    
  -- Step 3: Substitute the established equality into the valuation mismatch hypothesis.

  rw [h_eq] at h_val_mismatch
  
  -- Step 4: The mismatch hypothesis now asserts that a value is not equal to itself. 

  exact h_val_mismatch rfl

#check cycle_impossible_if_valuation_mismatch
#print axioms cycle_impossible_if_valuation_mismatch

--==================================================================
--Section 16A: Lemma 3D - Non-Equilibrium Z = 1 Handling
--==================================================================
section Section16_Lemma3D_Neutral_Branch

/--
Lemma 3D, Step 1.

The denominator deviation is the signed exponent deviation
`2^(S_n) - 2^(2n)`.
-/
lemma lemma_3D_DeltaD_signed (n x : ℕ) :
  Delta_D n x =
    (((2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n) : ℤ) : ℚ) := by

  have h_DeltaD_rat :
      Delta_D n x =
        (2 : ℚ)^(S n x) - (2 : ℚ)^(2 * n) := by
    unfold Delta_D D_new D_eq

    have h_le : 3^n ≤ 2^(2 * n) := by
      rw [pow_mul]
      exact Nat.pow_le_pow_left (by norm_num : 3 ≤ 2^2) n

    rw [Nat.cast_sub h_le]
    push_cast
    ring

  rw [h_DeltaD_rat]
  push_cast
  ring

/--
Lemma 3D, Step 2.

If the rational numerator deviation equals the rational denominator deviation,
then the corresponding signed integer deviations are equal.
-/
lemma lemma_3D_delta_equality_int_of_rat
  (n x : ℕ)
  (h_eq : ((delta_N_actual_inc n x : ℚ) = Delta_D n x)) :
  delta_N_actual_inc n x =
    (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n) := by

  have hD :=
    lemma_3D_DeltaD_signed n x

  rw [hD] at h_eq

  exact_mod_cast h_eq

/--
Lemma 3D, Step 3.

If every numerator-visible prefix is still in equilibrium, then equality of
the numerator and denominator deviations forces full equilibrium. Hence this
case contradicts `h_non_eq`.
-/
lemma lemma_3D_terminal_only_branch_closed
  (n x : ℕ)
  (h_non_eq : ¬ ∀ j ≤ n, S j x = 2 * j)
  (h_visible_eq : ∀ j ∈ Ico 1 n, S j x = 2 * j)
  (h_eq_int :
    delta_N_actual_inc n x =
      (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) :
  False := by

  have h_deltaN_zero :
      delta_N_actual_inc n x = 0 := by
    unfold delta_N_actual_inc
    apply sum_eq_zero
    intro j hj
    rw [h_visible_eq j hj]
    ring

  rw [h_deltaN_zero] at h_eq_int

  have h_sub_zero :
      (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n) = 0 := by
    exact h_eq_int.symm

  have h_pow_eq :
      (2 : ℤ)^(S n x) = (2 : ℤ)^(2 * n) := by
    exact sub_eq_zero.mp h_sub_zero

  have h_pow_eq_nat :
      2^(S n x) = 2^(2 * n) := by
    exact_mod_cast h_pow_eq

  have hSn :
      S n x = 2 * n := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt

    · have hpow_lt :
          2^(S n x) < 2^(2 * n) := by
        exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
      omega

    · have hpow_gt :
          2^(2 * n) < 2^(S n x) := by
        exact Nat.pow_lt_pow_right (by norm_num : 1 < 2) hgt
      omega

  apply h_non_eq
  intro j hj

  by_cases hjn : j = n

  · subst j
    exact hSn

  · have hj_lt : j < n := by omega

    by_cases hj0 : j = 0

    · subst j
      simp [S]

    · have hj_pos : 1 ≤ j :=
        Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)

      have hj_Ico : j ∈ Ico 1 n := by
        rw [mem_Ico]
        exact ⟨hj_pos, hj_lt⟩

      exact h_visible_eq j hj_Ico
/--
Lemma 3D, Step 4.

If the numerator-visible prefixes are not all equilibrium, then there is a
first visible deviation `r`, and all earlier visible prefixes are equilibrium.
-/
lemma lemma_3D_first_visible_deviation
  (n x : ℕ)
  (h_visible_ne : ¬ ∀ j ∈ Ico 1 n, S j x = 2 * j) :
  ∃ r,
    r ∈ Ico 1 n ∧
      S r x ≠ 2 * r ∧
        ∀ j ∈ Ico 1 r, S j x = 2 * j := by

  have h_exists_visible :
      ∃ r, r ∈ Ico 1 n ∧ S r x ≠ 2 * r := by
    by_contra h_none
    apply h_visible_ne
    intro j hj
    by_contra h_bad
    exact h_none ⟨j, hj, h_bad⟩

  let r := Nat.find h_exists_visible

  have hr_spec :
      r ∈ Ico 1 n ∧ S r x ≠ 2 * r :=
    Nat.find_spec h_exists_visible

  refine ⟨r, hr_spec.1, hr_spec.2, ?_⟩

  intro j hj
  by_contra h_bad

  have hr_lt_n : r < n :=
    (mem_Ico.mp hr_spec.1).2

  have hj_bounds :
      1 ≤ j ∧ j < r :=
    mem_Ico.mp hj

  have hj_mem_n : j ∈ Ico 1 n := by
    rw [mem_Ico]
    exact ⟨hj_bounds.1, lt_trans hj_bounds.2 hr_lt_n⟩

  have h_find_le :
      r ≤ j :=
    Nat.find_min' h_exists_visible ⟨hj_mem_n, h_bad⟩

  omega
/--
Lemma 3D, Step 5.

Under the physical validity condition `a_i >= 1`, prefix sums grow by at
least one per step after any starting index.
-/
lemma lemma_3D_prefix_growth
  (n x r : ℕ)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x)) :
  ∀ t, r + t ≤ n → S r x + t ≤ S (r + t) x := by

  intro t ht
  induction t with
  | zero =>
      simp

  | succ t ih =>
      have ht_prev : r + t ≤ n := by omega
      have h_idx_lt : r + t < n := by omega

      have h_step_valid :
          1 ≤ val ((T^[r + t]) x) :=
        h_valid (r + t) h_idx_lt

      have h_step :
          S (r + (t + 1)) x =
            S (r + t) x + val ((T^[r + t]) x) := by
        have h_add :
            r + (t + 1) = (r + t) + 1 := by
          omega
        rw [h_add, S]

      rw [h_step]

      have ih_prev :
          S r x + t ≤ S (r + t) x :=
        ih ht_prev

      omega
/--
Lemma 3D, Step 6.

At the first numerator-visible deviation `r`, the denominator deviation is
divisible by one more power of two than the first deviation floor.
-/
lemma lemma_3D_denominator_extra_two_dvd
  (n x r μ : ℕ)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x))
  (hr_lt : r < n)
  (hμ : μ = Nat.min (S r x) (2 * r)) :
  (2 : ℤ)^(μ + 1) ∣
    ((2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) := by

  have h_growth :
      S r x + (n - r) ≤ S n x := by
    have h :=
      lemma_3D_prefix_growth n x r h_valid (n - r) (by omega)
    rwa [Nat.add_sub_of_le (Nat.le_of_lt hr_lt)] at h

  have h_Sr_lt_Sn :
      S r x < S n x := by
    have h_gap : 0 < n - r := by omega
    omega

  have h_two_r_lt_two_n :
      2 * r < 2 * n := by
    omega

  have h_mu_lt_Sn :
      μ < S n x := by
    rw [hμ]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) h_Sr_lt_Sn

  have h_mu_lt_two_n :
      μ < 2 * n := by
    rw [hμ]
    exact lt_of_le_of_lt (Nat.min_le_right _ _) h_two_r_lt_two_n

  have h_mu_succ_le_Sn :
      μ + 1 ≤ S n x := by
    omega

  have h_mu_succ_le_two_n :
      μ + 1 ≤ 2 * n := by
    omega

  have h_left_dvd :
      (2 : ℤ)^(μ + 1) ∣ (2 : ℤ)^(S n x) := by
    use (2 : ℤ)^(S n x - (μ + 1))
    calc
      (2 : ℤ)^(S n x)
          =
        (2 : ℤ)^((μ + 1) + (S n x - (μ + 1))) := by
          congr 1
          omega
      _ =
        (2 : ℤ)^(μ + 1) *
          (2 : ℤ)^(S n x - (μ + 1)) := by
          rw [pow_add]

  have h_right_dvd :
      (2 : ℤ)^(μ + 1) ∣ (2 : ℤ)^(2 * n) := by
    use (2 : ℤ)^(2 * n - (μ + 1))
    calc
      (2 : ℤ)^(2 * n)
          =
        (2 : ℤ)^((μ + 1) + (2 * n - (μ + 1))) := by
          congr 1
          omega
      _ =
        (2 : ℤ)^(μ + 1) *
          (2 : ℤ)^(2 * n - (μ + 1)) := by
          rw [pow_add]

  exact dvd_sub h_left_dvd h_right_dvd
/--
Lemma 3D, Step 7.

Every numerator term strictly after the first visible deviation has the extra
factor `2^(μ+1)`.
-/
lemma lemma_3D_later_term_extra_two_dvd
  (n x r μ j : ℕ)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x))
  (hrj : r < j)
  (hj_lt : j < n)
  (hμ : μ = Nat.min (S r x) (2 * r)) :
  (2 : ℤ)^(μ + 1) ∣
    (3 : ℤ)^(n - 1 - j) *
      ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j)) := by

  have h_add_eq :
      r + (j - r) = j :=
    Nat.add_sub_of_le (Nat.le_of_lt hrj)

  have h_growth_j :
      S r x + (j - r) ≤ S j x := by
    have h_tmp :
        S r x + (j - r) ≤ S (r + (j - r)) x :=
      lemma_3D_prefix_growth n x r h_valid (j - r) (by
        rw [h_add_eq]
        exact Nat.le_of_lt hj_lt)
    rwa [h_add_eq] at h_tmp

  have h_gap_pos :
      1 ≤ j - r := by
    omega

  have h_mu_succ_le_Sj :
      μ + 1 ≤ S j x := by
    have h_mu_le_Sr : μ ≤ S r x := by
      rw [hμ]
      exact Nat.min_le_left _ _
    omega

  have h_mu_succ_le_twoj :
      μ + 1 ≤ 2 * j := by
    have h_mu_le_two_r : μ ≤ 2 * r := by
      rw [hμ]
      exact Nat.min_le_right _ _
    omega

  have h_left_dvd :
      (2 : ℤ)^(μ + 1) ∣ (2 : ℤ)^(S j x) := by
    use (2 : ℤ)^(S j x - (μ + 1))
    calc
      (2 : ℤ)^(S j x)
          =
        (2 : ℤ)^((μ + 1) + (S j x - (μ + 1))) := by
          congr 1
          omega
      _ =
        (2 : ℤ)^(μ + 1) *
          (2 : ℤ)^(S j x - (μ + 1)) := by
          rw [pow_add]

  have h_right_dvd :
      (2 : ℤ)^(μ + 1) ∣ (2 : ℤ)^(2 * j) := by
    use (2 : ℤ)^(2 * j - (μ + 1))
    calc
      (2 : ℤ)^(2 * j)
          =
        (2 : ℤ)^((μ + 1) + (2 * j - (μ + 1))) := by
          congr 1
          omega
      _ =
        (2 : ℤ)^(μ + 1) *
          (2 : ℤ)^(2 * j - (μ + 1)) := by
          rw [pow_add]

  have h_diff_dvd :
      (2 : ℤ)^(μ + 1) ∣
        ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j)) := by
    exact dvd_sub h_left_dvd h_right_dvd

  exact dvd_mul_of_dvd_right h_diff_dvd ((3 : ℤ)^(n - 1 - j))

/--
Lemma 3D, Step 8.

The first visible nonzero numerator term has exact 2-adic floor `μ`; hence it
is not divisible by the extra factor `2^(μ+1)`.
-/
lemma lemma_3D_first_term_not_extra_two_dvd
  (n x r μ : ℕ)
  (hr_ne : S r x ≠ 2 * r)
  (hμ : μ = Nat.min (S r x) (2 * r)) :
  ¬ (2 : ℤ)^(μ + 1) ∣
    (3 : ℤ)^(n - 1 - r) *
      ((2 : ℤ)^(S r x) - (2 : ℤ)^(2 * r)) := by

  intro h_dvd

  let A : ℕ := S r x
  let B : ℕ := 2 * r
  let c3 : ℤ := (3 : ℤ)^(n - 1 - r)

  have hAB_ne : A ≠ B := by
    dsimp [A, B]
    exact hr_ne

  have h_mu_AB :
      μ = Nat.min A B := by
    dsimp [A, B]
    exact hμ

  have h_c3_odd :
      (c3 : ZMod 2) = 1 := by
    dsimp [c3]
    push_cast
    have h3 : (3 : ZMod 2) = 1 := by
      decide
    rw [h3]
    simp

  have h_term_eq :
      (3 : ℤ)^(n - 1 - r) *
          ((2 : ℤ)^(S r x) - (2 : ℤ)^(2 * r))
        =
      c3 * ((2 : ℤ)^A - (2 : ℤ)^B) := by
    dsimp [A, B, c3]

  rw [h_term_eq] at h_dvd

  rcases lt_or_gt_of_ne hAB_ne with hA_lt | hB_lt

  · -- Case A < B, so μ = A.
    have h_mu_eq : μ = A := by
      rw [h_mu_AB]
      exact Nat.min_eq_left hA_lt.le

    let C : ℤ := c3 * (1 - (2 : ℤ)^(B - A))

    have hBpow :
        (2 : ℤ)^B = (2 : ℤ)^A * (2 : ℤ)^(B - A) := by
      calc
        (2 : ℤ)^B
            =
          (2 : ℤ)^(A + (B - A)) := by
            congr 1
            omega
        _ =
          (2 : ℤ)^A * (2 : ℤ)^(B - A) := by
            rw [pow_add]

    have h_factor :
        c3 * ((2 : ℤ)^A - (2 : ℤ)^B) =
          (2 : ℤ)^μ * C := by
      rw [h_mu_eq]
      dsimp [C]
      rw [hBpow]
      ring

    rw [h_factor] at h_dvd

    rcases h_dvd with ⟨q, hq⟩

    have h_pow_ne :
        (2 : ℤ)^μ ≠ 0 :=
      pow_ne_zero μ (by norm_num)

    have hC_even :
        C = 2 * q := by
      have h_eq :
          (2 : ℤ)^μ * C = (2 : ℤ)^μ * (2 * q) := by
        have h_rhs :
            (2 : ℤ)^(μ + 1) * q =
              (2 : ℤ)^μ * (2 * q) := by
          rw [pow_succ]
          ring
        rw [hq, h_rhs]
      exact mul_left_cancel₀ h_pow_ne h_eq

    have hC_zero :
        (C : ZMod 2) = 0 := by
      rw [hC_even]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by
        decide
      rw [h2]
      ring

    have h_gap_pos :
        0 < B - A := by
      omega

    have h_two_gap :
        ((2 : ZMod 2)^(B - A)) = 0 := by
      have h_gap_ne : B - A ≠ 0 := by
        omega
      cases hcase : B - A with
      | zero =>
          exact False.elim (h_gap_ne hcase)
      | succ d =>
          rw [pow_succ]
          have h2 : (2 : ZMod 2) = 0 := by
            decide
          rw [h2]
          ring

    have hC_one :
        (C : ZMod 2) = 1 := by
      dsimp [C]
      push_cast
      rw [h_c3_odd, h_two_gap]
      decide

    have h_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
      decide

    rw [hC_one] at hC_zero
    exact h_one_ne_zero hC_zero

  · -- Case B < A, so μ = B.
    have h_mu_eq : μ = B := by
      rw [h_mu_AB]
      exact Nat.min_eq_right hB_lt.le

    let C : ℤ := c3 * ((2 : ℤ)^(A - B) - 1)

    have hApow :
        (2 : ℤ)^A = (2 : ℤ)^B * (2 : ℤ)^(A - B) := by
      calc
        (2 : ℤ)^A
            =
          (2 : ℤ)^(B + (A - B)) := by
            congr 1
            omega
        _ =
          (2 : ℤ)^B * (2 : ℤ)^(A - B) := by
            rw [pow_add]

    have h_factor :
        c3 * ((2 : ℤ)^A - (2 : ℤ)^B) =
          (2 : ℤ)^μ * C := by
      rw [h_mu_eq]
      dsimp [C]
      rw [hApow]
      ring

    rw [h_factor] at h_dvd

    rcases h_dvd with ⟨q, hq⟩

    have h_pow_ne :
        (2 : ℤ)^μ ≠ 0 :=
      pow_ne_zero μ (by norm_num)

    have hC_even :
        C = 2 * q := by
      have h_eq :
          (2 : ℤ)^μ * C = (2 : ℤ)^μ * (2 * q) := by
        have h_rhs :
            (2 : ℤ)^(μ + 1) * q =
              (2 : ℤ)^μ * (2 * q) := by
          rw [pow_succ]
          ring
        rw [hq, h_rhs]
      exact mul_left_cancel₀ h_pow_ne h_eq

    have hC_zero :
        (C : ZMod 2) = 0 := by
      rw [hC_even]
      push_cast
      have h2 : (2 : ZMod 2) = 0 := by
        decide
      rw [h2]
      ring

    have h_gap_pos :
        0 < A - B := by
      omega

    have h_two_gap :
        ((2 : ZMod 2)^(A - B)) = 0 := by
      have h_gap_ne : A - B ≠ 0 := by
        omega
      cases hcase : A - B with
      | zero =>
          exact False.elim (h_gap_ne hcase)
      | succ d =>
          rw [pow_succ]
          have h2 : (2 : ZMod 2) = 0 := by
            decide
          rw [h2]
          ring

    have hC_one :
        (C : ZMod 2) = 1 := by
      dsimp [C]
      push_cast
      rw [h_c3_odd, h_two_gap]
      decide

    have h_one_ne_zero : (1 : ZMod 2) ≠ 0 := by
      decide

    rw [hC_one] at hC_zero
    exact h_one_ne_zero hC_zero

/--
Lemma 3D, Step 9.

If there is a first numerator-visible deviation, then equality of the actual
numerator deviation and denominator deviation is impossible.
-/
lemma lemma_3D_visible_branch_closed
  (n x r : ℕ)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x))
  (hr_mem : r ∈ Ico 1 n)
  (hr_ne : S r x ≠ 2 * r)
  (h_before : ∀ j ∈ Ico 1 r, S j x = 2 * j)
  (h_eq_int :
    delta_N_actual_inc n x =
      (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) :
  False := by

  let μ : ℕ := Nat.min (S r x) (2 * r)

  have hμ :
      μ = Nat.min (S r x) (2 * r) := by
    rfl

  have hr_lt : r < n :=
    (mem_Ico.mp hr_mem).2

  have h_den_dvd :
      (2 : ℤ)^(μ + 1) ∣
        ((2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n)) :=
    lemma_3D_denominator_extra_two_dvd
      n x r μ h_valid hr_lt hμ

  have h_deltaN_dvd :
      (2 : ℤ)^(μ + 1) ∣ delta_N_actual_inc n x := by
    rw [h_eq_int]
    exact h_den_dvd

  let M : ℤ := (2 : ℤ)^(μ + 1)

  have h_deltaN_dvd_M :
      M ∣ delta_N_actual_inc n x := by
    dsimp [M]
    exact h_deltaN_dvd

  let f : ℕ → ℤ :=
    fun j =>
      (3 : ℤ)^(n - 1 - j) *
        ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j))

  have h_deltaN_split :
      delta_N_actual_inc n x =
        (∑ j ∈ (Ico 1 n).erase r, f j) + f r := by
    unfold delta_N_actual_inc
    dsimp [f]
    rw [← sum_erase_add _ _ hr_mem]

  have h_rest_dvd :
      M ∣ ∑ j ∈ (Ico 1 n).erase r, f j := by
    apply dvd_sum
    intro j hj

    have hj_parts := mem_erase.mp hj
    have hj_ne_r : j ≠ r := hj_parts.1
    have hj_mem_n : j ∈ Ico 1 n := hj_parts.2

    by_cases hj_lt_r : j < r

    · have hj_mem_r : j ∈ Ico 1 r := by
        rw [mem_Ico] at hj_mem_n ⊢
        exact ⟨hj_mem_n.1, hj_lt_r⟩

      have hfj_zero : f j = 0 := by
        dsimp [f]
        rw [h_before j hj_mem_r]
        ring

      rw [hfj_zero]
      exact dvd_zero M

    · have hr_lt_j : r < j := by
        omega

      have hj_lt_n : j < n :=
        (mem_Ico.mp hj_mem_n).2

      have h_later :
          (2 : ℤ)^(μ + 1) ∣
            (3 : ℤ)^(n - 1 - j) *
              ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j)) :=
        lemma_3D_later_term_extra_two_dvd
          n x r μ j h_valid hr_lt_j hj_lt_n hμ

      dsimp [M, f]
      exact h_later

  let R : ℤ := ∑ j ∈ (Ico 1 n).erase r, f j

  have h_sum_dvd :
      M ∣ R + f r := by
    dsimp [R]
    rw [← h_deltaN_split]
    exact h_deltaN_dvd_M

  have h_rest_dvd_R :
      M ∣ R := by
    dsimp [R]
    exact h_rest_dvd

  have h_fr_dvd :
      M ∣ f r := by
    have h_raw :
        M ∣ (R + f r) - R :=
      dvd_sub h_sum_dvd h_rest_dvd_R

    have h_simp :
        (R + f r) - R = f r := by
      ring

    rwa [h_simp] at h_raw

  have h_first_not :
      ¬ (2 : ℤ)^(μ + 1) ∣
        (3 : ℤ)^(n - 1 - r) *
          ((2 : ℤ)^(S r x) - (2 : ℤ)^(2 * r)) :=
    lemma_3D_first_term_not_extra_two_dvd n x r μ hr_ne hμ

  apply h_first_not

  dsimp [M, f] at h_fr_dvd
  exact h_fr_dvd

/--
Lemma 3D.

For any valid non-equilibrium exponent profile, the actual numerator deviation
cannot equal the denominator deviation. This closes the non-equilibrium
neutral branch `Z = 1`.
-/
theorem lemma_3D_non_equilibrium_delta_misalignment
  (n x : ℕ)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x))
  (h_non_eq : ¬ ∀ j ≤ n, S j x = 2 * j) :
  ((delta_N_actual_inc n x : ℚ) ≠ Delta_D n x) := by

  intro h_eq_rat

  have h_eq_int :
      delta_N_actual_inc n x =
        (2 : ℤ)^(S n x) - (2 : ℤ)^(2 * n) :=
    lemma_3D_delta_equality_int_of_rat n x h_eq_rat

  by_cases h_visible_eq :
      ∀ j ∈ Ico 1 n, S j x = 2 * j

  · exact
      lemma_3D_terminal_only_branch_closed
        n x h_non_eq h_visible_eq h_eq_int

  · rcases
      lemma_3D_first_visible_deviation n x h_visible_eq
        with ⟨r, hr_mem, hr_ne, h_before⟩

    exact
      lemma_3D_visible_branch_closed
        n x r h_valid hr_mem hr_ne h_before h_eq_int

end Section16_Lemma3D_Neutral_Branch


#check lemma_3D_DeltaD_signed
#check lemma_3D_delta_equality_int_of_rat
#check lemma_3D_terminal_only_branch_closed
#check lemma_3D_first_visible_deviation
#check lemma_3D_prefix_growth
#check lemma_3D_later_term_extra_two_dvd
#check lemma_3D_denominator_extra_two_dvd
#check lemma_3D_later_term_extra_two_dvd
#check lemma_3D_first_term_not_extra_two_dvd
#check lemma_3D_visible_branch_closed
#check lemma_3D_non_equilibrium_delta_misalignment
#print axioms lemma_3D_non_equilibrium_delta_misalignment
-- ===============================================================
-- SECTION 17: LEMMA 1E - PARITY LEMMA
-- ===============================================================

section Section17_Lemma1E_ParityLemma

/--
In `ZMod 2`, the numeral `2` is zero.
-/
lemma zmod_two_two_eq_zero : (2 : ZMod 2) = 0 := by
  decide

/--
In `ZMod 2`, every element added to itself is zero.
-/
lemma zmod_two_add_self_eq_zero (a : ZMod 2) :
  a + a = 0 := by
  calc
    a + a = (2 : ZMod 2) * a := by ring
    _ = 0 * a := by rw [zmod_two_two_eq_zero]
    _ = 0 := by ring

/--
Prefix perturbation recursion.

`S'_{k+1} = S'_k + δ_k`.
-/
lemma S_prime_succ
  (x k : ℕ) :
  S_prime (k + 1) x = S_prime k x + delta x k := by

  unfold S_prime
  rw [sum_range_succ]

/--
Modulo-2 form of the local perturbation.

Since `δ_k = a_k - 2`, modulo 2 it has the same parity as the physical
step size `a_k = val (T^[k] x)`.
-/
lemma delta_zmod_two_eq_val
  (x k : ℕ) :
  (delta x k : ZMod 2) = (val ((T^[k]) x) : ZMod 2) := by

  unfold delta

  calc
    (((val ((T^[k]) x) : ℤ) - 2 : ℤ) : ZMod 2)
        =
      (val ((T^[k]) x) : ZMod 2) - (2 : ZMod 2) := by
        push_cast
        ring
    _ =
      (val ((T^[k]) x) : ZMod 2) := by
        rw [zmod_two_two_eq_zero]
        ring

/--
Lemma 1E core congruence.

Manuscript form:
`d_{k+1} ≡ d_k + a_k (mod 2)`.

In the existing formalization, the signed prefix deviation is `S'_k`, and
absolute value does not change parity, so the operative congruence is:
`S'_{k+1} ≡ S'_k + a_k (mod 2)`.
-/
theorem lemma_1E_parity_congruence
  (x k : ℕ) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + (val ((T^[k]) x) : ZMod 2) := by

  rw [S_prime_succ x k]

  have h_cast :
      ((S_prime k x + delta x k : ℤ) : ZMod 2) =
        (S_prime k x : ZMod 2) + (delta x k : ZMod 2) := by
    exact Int.cast_add (S_prime k x) (delta x k)

  calc
    ((S_prime k x + delta x k : ℤ) : ZMod 2)
        =
      (S_prime k x : ZMod 2) + (delta x k : ZMod 2) := h_cast
    _ =
      (S_prime k x : ZMod 2) + (val ((T^[k]) x) : ZMod 2) := by
        rw [delta_zmod_two_eq_val x k]
/--
Even physical steps preserve prefix-deviation parity.
-/
theorem lemma_1E_even_step_preserves_parity
  (x k : ℕ)
  (h_even : Even (val ((T^[k]) x))) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) := by

  rw [lemma_1E_parity_congruence x k]

  rcases h_even with ⟨t, ht⟩

  have h_val_zero :
      (val ((T^[k]) x) : ZMod 2) = 0 := by
    rw [ht]
    rw [Nat.cast_add]
    exact zmod_two_add_self_eq_zero (t : ZMod 2)

  rw [h_val_zero]
  ring

/--
Odd physical steps invert prefix-deviation parity.
-/
theorem lemma_1E_odd_step_inverts_parity
  (x k : ℕ)
  (h_odd : Odd (val ((T^[k]) x))) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + 1 := by

  rw [lemma_1E_parity_congruence x k]

  rcases h_odd with ⟨t, ht⟩

  have h_val_one :
      (val ((T^[k]) x) : ZMod 2) = 1 := by
    rw [ht]

    calc
      ((2 * t + 1 : ℕ) : ZMod 2)
          =
        (2 : ZMod 2) * (t : ZMod 2) + 1 := by
          push_cast
          ring
      _ =
        0 * (t : ZMod 2) + 1 := by
          rw [zmod_two_two_eq_zero]
      _ =
        1 := by ring

  rw [h_val_one]

/--
The negative perturbation case `a_k = 1` is an odd step, hence it inverts
prefix-deviation parity.
-/
theorem lemma_1E_negative_step_inverts_parity
  (x k : ℕ)
  (h_neg : val ((T^[k]) x) = 1) :
  (S_prime (k + 1) x : ZMod 2) =
    (S_prime k x : ZMod 2) + 1 := by

  apply lemma_1E_odd_step_inverts_parity x k
  rw [h_neg]
  exact ⟨0, by norm_num⟩

end Section17_Lemma1E_ParityLemma

-- ===============================================================
-- SECTION 18: LEMMA 1F (LHS BIFURCATION)
-- ===============================================================
section Section18_Lemma1F

/-- Generic sequence term T_k -/
noncomputable def T_seq (n x k : ℕ) : ℤ :=
  (3 : ℤ)^(n - 1 - k) * ((2 : ℤ)^(S k x) - (2 : ℤ)^(2 * k))

/-- Integer Equilibrium Numerator Summation Identity -/
theorem N_eq_as_sum_int (n : ℕ) :
  (N_eq n : ℤ) = ∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(2 * j) := by
  rw [N_eq]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]

    have h_factor :
        ∑ j ∈ range m, (3 : ℤ) ^ (m.succ - 1 - j) * (2 : ℤ) ^ (2 * j) =
          3 * ∑ j ∈ range m, (3 : ℤ) ^ (m - 1 - j) * (2 : ℤ) ^ (2 * j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j hj
      rw [nat_index_shift m j (Finset.mem_range.mp hj), pow_succ]
      ring

    rw [h_factor, ← ih]

    have h_pow_match : (2 : ℤ) ^ (2 * m) = (4 : ℤ) ^ m := by
      rw [pow_mul]
      norm_num

    simp only [Nat.succ_sub_one, Nat.sub_self, pow_zero, one_mul, h_pow_match]

    have h_le_succ : 3^(m + 1) ≤ 4^(m + 1) :=
      Nat.pow_le_pow_left (by norm_num) (m + 1)
    have h_le_m : 3^m ≤ 4^m :=
      Nat.pow_le_pow_left (by norm_num) m

    rw [Nat.cast_sub h_le_succ, Nat.cast_sub h_le_m]
    push_cast
    ring

/-- The Z-ring summation bridge. -/
theorem lemma_delta_equiv_bridge (n x : ℕ) (hn : 0 < n) :
  (sum_T n x : ℤ) - (N_eq n : ℤ) = delta_N_actual_inc n x := by
  dsimp [sum_T, delta_N_actual_inc]
  push_cast
  rw [N_eq_as_sum_int n]

  have h_combined_sum :
      (∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(S j x)) -
        (∑ j ∈ range n, (3 : ℤ)^(n - 1 - j) * (2 : ℤ)^(2 * j))
      =
        ∑ j ∈ range n, T_seq n x j := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j _
    dsimp [T_seq]
    ring

  rw [h_combined_sum]

  have h_range_split : range n = insert 0 (Ico 1 n) := by
    ext a
    simp only [mem_range, mem_insert, mem_Ico]
    omega

  have h_not_in : 0 ∉ Ico 1 n := by
    simp only [mem_Ico, not_and]
    intro h
    omega

  have h_split_range :
      ∑ j ∈ range n, T_seq n x j =
        T_seq n x 0 + ∑ j ∈ Ico 1 n, T_seq n x j := by
    rw [h_range_split]
    exact sum_insert h_not_in

  rw [h_split_range]

  have h_term_zero : T_seq n x 0 = 0 := by
    dsimp [T_seq, S]
    ring

  rw [h_term_zero, zero_add]
  unfold T_seq
  rfl

/--
Lemma 3D, cycle-facing bridge.

If a cycle has seed/ratio `x = 1`, then the actual numerator increment equals
the denominator increment.
-/
lemma lemma_3D_cycle_one_delta_identity
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x = 1) :
  ((delta_N_actual_inc n x : ℚ) = Delta_D n x) := by

  subst x

  have h_int :
      delta_N_actual_inc n 1 =
        (2 : ℤ)^(S n 1) - (2 : ℤ)^(2 * n) := by
    have h_2D :=
      lemma_2D_increment_stepwise n 1 h_cycle hn
    rw [lemma_delta_equiv_bridge n 1 hn] at h_2D
    simpa using h_2D

  have h_rat :
      (delta_N_actual_inc n 1 : ℚ) =
        (((2 : ℤ)^(S n 1) - (2 : ℤ)^(2 * n) : ℤ) : ℚ) := by
    exact_mod_cast h_int

  rw [h_rat]
  exact (lemma_3D_DeltaD_signed n 1).symm

#check lemma_3D_cycle_one_delta_identity
#print axioms lemma_3D_cycle_one_delta_identity

/--
Lemma 3D, cycle-facing closure.

A cycle with `x = 1` cannot be non-equilibrium. Therefore the neutral branch
`Z = 1` forces the equilibrium exponent profile.
-/
theorem lemma_3D_cycle_one_forces_equilibrium
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (h_valid : ∀ i < n, 1 ≤ val ((T^[i]) x))
  (hx : x = 1) :
  ∀ j ≤ n, S j x = 2 * j := by

  by_contra h_non_eq

  have h_delta_eq :
      ((delta_N_actual_inc n x : ℚ) = Delta_D n x) :=
    lemma_3D_cycle_one_delta_identity n x h_cycle hn hx

  exact
    (lemma_3D_non_equilibrium_delta_misalignment
      n x h_valid h_non_eq)
    h_delta_eq

#check lemma_3D_cycle_one_forces_equilibrium
#print axioms lemma_3D_cycle_one_forces_equilibrium

/-- Offset variable B. -/
noncomputable def offset_B (n x : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n) - (x : ℤ) * (2 : ℤ)^(S n x)

/-- Terminal boundary grouping T_last. -/
noncomputable def T_last (n x : ℕ) : ℤ :=
  (3 : ℤ)^0 * ((2 : ℤ)^(S (n - 1) x) - (2 : ℤ)^(2 * (n - 1))) + offset_B n x

/-- Internal sum in the bifurcated Lemma 1F equation. -/
noncomputable def internal_T_sum (n x : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 (n - 1), T_seq n x k

/-- Full bifurcated LHS. -/
noncomputable def bifurcated_LHS (n x : ℕ) : ℤ :=
  internal_T_sum n x + T_last n x

/-- Bifurcated component: internal terms plus terminal `T_last`. -/
noncomputable def bifurcated_component (n x k : ℕ) : ℤ :=
  if k = n - 1 then T_last n x else T_seq n x k

/-- A bifurcated component reaches a target 3-adic valuation. -/
def bifurcated_component_reaches_target (n x target k : ℕ) : Prop :=
  (3 : ℤ)^target ∣ bifurcated_component n x k

/--
Step 1: The bifurcated structure, derived from Lemma 2D.
-/
theorem lemma_1F_step1_bifurcation
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (∑ k ∈ Ico 1 (n - 1), T_seq n x k) + T_last n x =
    (1 - (x : ℤ)) * (3 : ℤ)^n := by

  have hn_pos : 0 < n := by omega
  have h_delta_equiv := lemma_delta_equiv_bridge n x hn_pos
  have h_2D := lemma_2D_increment_stepwise n x h_cycle hn_pos

  have h_mod_cycle :
      delta_N_actual_inc n x + offset_B n x =
        (1 - (x : ℤ)) * (3 : ℤ)^n := by
    rw [← h_delta_equiv]
    dsimp [offset_B]
    linarith [h_2D]

  have h_sum_def :
      delta_N_actual_inc n x = ∑ k ∈ Ico 1 n, T_seq n x k := by
    unfold delta_N_actual_inc T_seq
    apply sum_congr rfl
    intro k _
    rfl

  rw [h_sum_def] at h_mod_cycle

  have h_ico_split : Ico 1 n = insert (n - 1) (Ico 1 (n - 1)) := by
    ext a
    simp only [mem_Ico, mem_insert]
    omega

  have h_not_in_ico : n - 1 ∉ Ico 1 (n - 1) := by
    simp only [mem_Ico, not_and, not_lt]
    intro _
    omega

  have h_split :
      ∑ k ∈ Ico 1 n, T_seq n x k =
        T_seq n x (n - 1) + ∑ k ∈ Ico 1 (n - 1), T_seq n x k := by
    rw [h_ico_split]
    exact sum_insert h_not_in_ico

  rw [h_split] at h_mod_cycle

  have h_T_last_eq : T_seq n x (n - 1) + offset_B n x = T_last n x := by
    dsimp [T_seq, T_last]
    have h_zero : n - 1 - (n - 1) = 0 := by omega
    rw [h_zero]
    ring

  have h_rearrange :
      (T_seq n x (n - 1) + ∑ k ∈ Ico 1 (n - 1), T_seq n x k) + offset_B n x =
        (∑ k ∈ Ico 1 (n - 1), T_seq n x k) +
          (T_seq n x (n - 1) + offset_B n x) := by
    ring

  rw [h_rearrange] at h_mod_cycle
  rw [h_T_last_eq] at h_mod_cycle
  exact h_mod_cycle

/-- Lemma 1F in normalized LHS form. -/
theorem lemma_1F_step1_bifurcated_LHS_eq
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  bifurcated_LHS n x = (1 - (x : ℤ)) * (3 : ℤ)^n := by
  unfold bifurcated_LHS internal_T_sum
  exact lemma_1F_step1_bifurcation n x h_cycle hn

/-- The bifurcated LHS is the sum of bifurcated components. -/
lemma bifurcated_LHS_eq_component_sum
  (n x : ℕ) (hn : 1 < n) :
  bifurcated_LHS n x =
    ∑ k ∈ Ico 1 n, bifurcated_component n x k := by

  unfold bifurcated_LHS internal_T_sum bifurcated_component

  have h_split : Ico 1 n = insert (n - 1) (Ico 1 (n - 1)) := by
    ext a
    simp only [mem_Ico, mem_insert]
    omega

  have h_not_in : n - 1 ∉ Ico 1 (n - 1) := by
    simp only [mem_Ico]
    omega

  rw [h_split]
  rw [sum_insert h_not_in]

  have h_internal :
      ∑ k ∈ Ico 1 (n - 1),
        (if k = n - 1 then T_last n x else T_seq n x k)
      =
      ∑ k ∈ Ico 1 (n - 1), T_seq n x k := by
    apply sum_congr rfl
    intro k hk
    have hk_ne : k ≠ n - 1 := by
      rw [mem_Ico] at hk
      omega
    simp [hk_ne]

  simp
  rw [h_internal]
  ring

/-- Internal part of the bifurcated LHS is divisible by 3. -/
lemma lemma_1F_internal_sum_divisible_by_three
  (n x : ℕ) (hn : 1 < n) :
  (3 : ℤ) ∣ internal_T_sum n x := by
  unfold internal_T_sum
  apply dvd_sum
  intro k hk
  have hk_lt : k < n - 1 := (mem_Ico.mp hk).2
  have h_exp_pos : 1 ≤ n - 1 - k := by omega
  have h_positional : (3 : ℤ) ∣ (3 : ℤ)^(n - 1 - k) := by
    simpa using (pow_dvd_pow (3 : ℤ) h_exp_pos)
  unfold T_seq
  exact dvd_mul_of_dvd_left h_positional _

/--
Step 2: `T_last` must participate 3-adically.

Thus the case `v₃(T_last) = 0` is impossible for a cycle.
-/
theorem lemma_1F_step2_T_last_divisible_by_three
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (3 : ℤ) ∣ T_last n x := by

  have h_lhs_eq := lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn

  have h_rhs_dvd :
      (3 : ℤ) ∣ (1 - (x : ℤ)) * (3 : ℤ)^n := by
    have h_pow_dvd : (3 : ℤ) ∣ (3 : ℤ)^n := by
      simpa using (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ n))
    exact dvd_mul_of_dvd_right h_pow_dvd (1 - (x : ℤ))

  have h_lhs_dvd : (3 : ℤ) ∣ bifurcated_LHS n x := by
    rw [h_lhs_eq]
    exact h_rhs_dvd

  have h_internal_dvd := lemma_1F_internal_sum_divisible_by_three n x hn

  have h_T_last_eq :
      T_last n x = bifurcated_LHS n x - internal_T_sum n x := by
    unfold bifurcated_LHS
    ring

  rw [h_T_last_eq]
  exact dvd_sub h_lhs_dvd h_internal_dvd

/-- Contradiction form of Step 2. -/
theorem lemma_1F_step2_T_last_zero_valuation_contradiction
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n)
  (h_T_last_zero : ¬ (3 : ℤ) ∣ T_last n x) :
  False := by
  exact h_T_last_zero
    (lemma_1F_step2_T_last_divisible_by_three n x h_cycle hn)

/-- Integer divisibility bridge from `padicValNat` of `natAbs`. -/

lemma int_pow_three_padicValNat_abs_dvd
  (z : ℤ) (hz_ne : z ≠ 0) :
  (3 : ℤ)^(padicValNat 3 z.natAbs) ∣ z := by

  have hz_abs_ne : z.natAbs ≠ 0 := by
    intro h
    exact hz_ne (Int.natAbs_eq_zero.mp h)

  have h_nat_dvd : 3^(padicValNat 3 z.natAbs) ∣ z.natAbs := by
    exact
      (pow_dvd_iff_le_padicValNat
        (by norm_num : 3 ≠ 1) hz_abs_ne).mpr (le_refl _)

  rcases h_nat_dvd with ⟨c, hc⟩

  have hc_int :
      (z.natAbs : ℤ) =
        ((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ) := by
    exact_mod_cast hc

  by_cases hz_nonneg : 0 ≤ z
  · use (c : ℤ)
    have hz_abs_cast : (z.natAbs : ℤ) = z := by omega
    calc z = (z.natAbs : ℤ) := hz_abs_cast.symm
      _ = ((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ) := hc_int
      _ = (3 : ℤ)^(padicValNat 3 z.natAbs) * (c : ℤ) := by
          push_cast
          ring

  · use -(c : ℤ)
    have hz_abs_cast : (z.natAbs : ℤ) = -z := by omega
    calc z = -((z.natAbs : ℤ)) := by omega
      _ = -(((3^(padicValNat 3 z.natAbs) * c : ℕ) : ℤ)) := by
          rw [hc_int]
      _ = (3 : ℤ)^(padicValNat 3 z.natAbs) * (-(c : ℤ)) := by
          push_cast
          ring
#check int_pow_three_padicValNat_abs_dvd
#print axioms int_pow_three_padicValNat_abs_dvd
/--
The full 3-adic target forced by the bifurcated RHS.

The bifurcated equation has RHS `(1 - x) * 3^n`, so the target is
`n + v₃(|1 - x|)`.
-/
noncomputable def cycle_seed_target (n x : ℕ) : ℕ :=
  n + padicValNat 3 ((1 - (x : ℤ)).natAbs)

/-- Named target-reaching predicate for the bifurcated LHS. -/
def bifurcated_LHS_reaches_target (n x target : ℕ) : Prop :=
  (3 : ℤ)^target ∣ bifurcated_LHS n x

/-- The old `n` target remains true, but the seed target below is sharper. -/
theorem bifurcated_LHS_reaches_n
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  (3 : ℤ)^n ∣ bifurcated_LHS n x := by
  rw [lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn]
  exact dvd_mul_left ((3 : ℤ)^n) (1 - (x : ℤ))
#check bifurcated_LHS_reaches_n
#print axioms bifurcated_LHS_reaches_n

theorem cycle_bifurcated_LHS_reaches_target_n
  (n x : ℕ) (h_cycle : is_cycle n x) (hn : 1 < n) :
  bifurcated_LHS_reaches_target n x n := by
  unfold bifurcated_LHS_reaches_target
  exact bifurcated_LHS_reaches_n n x h_cycle hn
#check cycle_bifurcated_LHS_reaches_target_n
#print axioms cycle_bifurcated_LHS_reaches_target_n
/--
For a nontrivial cycle seed `x > 1`, the bifurcated LHS reaches the full
target `n + v₃(|1 - x|)`.
-/
theorem bifurcated_LHS_reaches_seed_target
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  (3 : ℤ)^(cycle_seed_target n x) ∣ bifurcated_LHS n x := by

  unfold cycle_seed_target
  rw [lemma_1F_step1_bifurcated_LHS_eq n x h_cycle hn]

  let A : ℤ := 1 - (x : ℤ)
  let e : ℕ := padicValNat 3 A.natAbs

  have hA_ne : A ≠ 0 := by
    dsimp [A]
    omega

  have hA_dvd : (3 : ℤ)^e ∣ A := by
    dsimp [e]
    exact int_pow_three_padicValNat_abs_dvd A hA_ne

  rcases hA_dvd with ⟨c, hc⟩
  use c

  have h_target_exp :
      n + padicValNat 3 (1 - (x : ℤ)).natAbs = n + e := by
    dsimp [e, A]

  rw [h_target_exp]

  calc
    (1 - (x : ℤ)) * (3 : ℤ)^n
        = A * (3 : ℤ)^n := by rfl
    _ = ((3 : ℤ)^e * c) * (3 : ℤ)^n := by rw [hc]
    _ = (3 : ℤ)^(e + n) * c := by
        rw [pow_add]
        ring
    _ = (3 : ℤ)^(n + e) * c := by
        rw [add_comm]

theorem cycle_bifurcated_LHS_reaches_seed_target
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  bifurcated_LHS_reaches_target n x (cycle_seed_target n x) := by
  unfold bifurcated_LHS_reaches_target
  exact bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

/--
Step 3: Sovereign cancellation.

If the whole bifurcated LHS reaches a cycle-forced target, and the rest of the
LHS also reaches a lower/equal target, then the skipped component must reach it
too. Therefore a skipped component gives contradiction.
-/
theorem lemma_1F_step3_sovereign_cancellation
  (n x j target : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_skipped :
    ¬ bifurcated_component_reaches_target n x target j)
  (h_rest_lifted :
    (3 : ℤ)^target ∣
      bifurcated_LHS n x - bifurcated_component n x j) :
  False := by

  have h_seed :
      (3 : ℤ)^(cycle_seed_target n x) ∣ bifurcated_LHS n x :=
    bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

  have h_target_dvd_seed :
      (3 : ℤ)^target ∣ (3 : ℤ)^(cycle_seed_target n x) :=
    pow_dvd_pow (3 : ℤ) h_target_le

  have h_lhs_target :
      (3 : ℤ)^target ∣ bifurcated_LHS n x :=
    dvd_trans h_target_dvd_seed h_seed

  have h_component_target :
      bifurcated_component_reaches_target n x target j := by
    unfold bifurcated_component_reaches_target
    have h_eq :
        bifurcated_component n x j =
          bifurcated_LHS n x -
            (bifurcated_LHS n x - bifurcated_component n x j) := by
      ring
    rw [h_eq]
    exact dvd_sub h_lhs_target h_rest_lifted

  exact h_skipped h_component_target

end Section18_Lemma1F

#check lemma_1F_step1_bifurcation
#check lemma_1F_step1_bifurcated_LHS_eq
#check lemma_1F_step2_T_last_divisible_by_three
#check lemma_1F_step2_T_last_zero_valuation_contradiction
#check bifurcated_LHS_reaches_seed_target
#check lemma_1F_step3_sovereign_cancellation
#print axioms lemma_1F_step3_sovereign_cancellation

-- ===============================================================
-- SECTION 19: LEMMA 1G (QUANTITATIVE LTE LIFT)
-- ===============================================================
section Section19_Lemma1G_Quantitative_LTE

/--
Internal term factorization.

If `S_k = 2k + d_k`, then the internal term splits into:
positional 3-power × equilibrium 2-power × lift factor `(2^d_k - 1)`.
-/
lemma T_seq_factor_of_prefix_deviation
  (n x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k) :
  T_seq n x k =
    (3 : ℤ)^(n - 1 - k) * (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
  unfold T_seq
  rw [hS, pow_add]
  ring
#check T_seq_factor_of_prefix_deviation
#print axioms T_seq_factor_of_prefix_deviation
/--
Step 1: Valuation deficit isolation.

If an internal term reaches target `p`, then after removing its positional
3-power, the lift factor `(2^d_k - 1)` must supply the remaining deficit.
-/
theorem lemma_1G_step1_valuation_deficit
  (n k p S_k d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (h_Sk : S_k = 2 * k + d_k)
  (h_T_div :
    (3 : ℤ)^p ∣
      (3 : ℤ)^(n - 1 - k) *
        ((2 : ℤ)^S_k - (2 : ℤ)^(2 * k))) :
  (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) := by

  have h_factor :
      (2 : ℤ)^S_k - (2 : ℤ)^(2 * k) =
        (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
    calc
      (2 : ℤ)^S_k - (2 : ℤ)^(2 * k)
          = (2 : ℤ)^(2 * k + d_k) - (2 : ℤ)^(2 * k) := by rw [h_Sk]
      _ = (2 : ℤ)^(2 * k) * (2 : ℤ)^d_k - (2 : ℤ)^(2 * k) * 1 := by
          rw [pow_add]
          ring
      _ = (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by ring

  have h_T_div_sub :
      (3 : ℤ)^p ∣
        (3 : ℤ)^(n - 1 - k) *
          ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    simpa [h_factor] using h_T_div

  have h_p_split : p = (n - 1 - k) + (p - (n - 1 - k)) := by
    omega

  have h_T_div_split :
      (3 : ℤ)^((n - 1 - k) + (p - (n - 1 - k))) ∣
        (3 : ℤ)^(n - 1 - k) *
          ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    rw [← h_p_split]
    exact h_T_div_sub

  rw [pow_add] at h_T_div_split

  have h_ne_zero : (3 : ℤ)^(n - 1 - k) ≠ 0 :=
    pow_ne_zero _ (by norm_num)

  have h_cancel :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        (2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1) := by
    exact (mul_dvd_mul_iff_left h_ne_zero).mp h_T_div_split

  have h_coprime :
      IsCoprime
        ((3 : ℤ)^(p - (n - 1 - k)))
        ((2 : ℤ)^(2 * k)) := by
    have h_base : IsCoprime (3 : ℤ) (2 : ℤ) := ⟨1, -1, by norm_num⟩
    exact IsCoprime.pow h_base

  rcases h_coprime with ⟨u, v, huv⟩

  have h_target_eq :
      ((2 : ℤ)^d_k - 1) =
        u * ((3 : ℤ)^(p - (n - 1 - k))) * ((2 : ℤ)^d_k - 1) +
          v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    calc
      ((2 : ℤ)^d_k - 1)
          = 1 * ((2 : ℤ)^d_k - 1) := by ring
      _ = (u * (3 : ℤ)^(p - (n - 1 - k)) +
            v * (2 : ℤ)^(2 * k)) * ((2 : ℤ)^d_k - 1) := by
          rw [← huv]
      _ =
          u * (3 : ℤ)^(p - (n - 1 - k)) * ((2 : ℤ)^d_k - 1) +
            v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by ring

  have h_dvd_term1 :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        u * ((3 : ℤ)^(p - (n - 1 - k))) * ((2 : ℤ)^d_k - 1) := by
    use u * ((2 : ℤ)^d_k - 1)
    ring

  rcases h_cancel with ⟨w, hw⟩

  have h_dvd_term2 :
      (3 : ℤ)^(p - (n - 1 - k)) ∣
        v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1)) := by
    use v * w
    calc
      v * ((2 : ℤ)^(2 * k) * ((2 : ℤ)^d_k - 1))
          = v * ((3 : ℤ)^(p - (n - 1 - k)) * w) := by rw [hw]
      _ = (3 : ℤ)^(p - (n - 1 - k)) * (v * w) := by ring

  rw [h_target_eq]
  exact dvd_add h_dvd_term1 h_dvd_term2
#check lemma_1G_step1_valuation_deficit
#print axioms lemma_1G_step1_valuation_deficit
/--
Modulo-3 LTE gateway.

If `3 ∣ 2^d - 1`, then `d` is even.
This is only a local prerequisite for the LTE calculation.
-/
lemma even_of_three_dvd_two_pow_sub_one
  (d : ℕ)
  (h_dvd : (3 : ℤ) ∣ (2 : ℤ)^d - 1) :
  Even d := by

  by_contra h_not_even

  have h_odd : Odd d := Nat.not_even_iff_odd.mp h_not_even
  rcases h_odd with ⟨t, ht⟩

  have h_pow_eq_one : (2 : ZMod 3)^d = 1 := by
    have h_zero :
        (((2 : ℤ)^d - 1 : ℤ) : ZMod 3) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h_dvd

    have h_cast :
        (((2 : ℤ)^d - 1 : ℤ) : ZMod 3) =
          (2 : ZMod 3)^d - 1 := by
      norm_num

    rw [h_cast] at h_zero
    exact sub_eq_zero.mp h_zero

  have h_pow_eq_two : (2 : ZMod 3)^d = 2 := by
    rw [ht]

    have h_two_sq : (2 : ZMod 3)^2 = 1 := by
      decide

    calc
      (2 : ZMod 3)^(2 * t + 1)
          = (2 : ZMod 3)^(2 * t) * 2 := by
              rw [pow_add]
              norm_num
      _ = ((2 : ZMod 3)^2)^t * 2 := by
              rw [pow_mul]
      _ = 1^t * 2 := by
              rw [h_two_sq]
      _ = 2 := by simp

  have h_contra : (1 : ZMod 3) = 2 := by
    rw [← h_pow_eq_one, h_pow_eq_two]

  have h_ne : (1 : ZMod 3) ≠ 2 := by
    decide

  exact h_ne h_contra
#check even_of_three_dvd_two_pow_sub_one
#print axioms even_of_three_dvd_two_pow_sub_one
/--
Deficit divisibility with a positive deficit forces the deviation exponent even.
-/
lemma lemma_1G_even_deviation_of_positive_deficit
  (q d : ℕ)
  (hq : 0 < q)
  (h_dvd : (3 : ℤ)^q ∣ ((2 : ℤ)^d - 1)) :
  Even d := by

  have h_three_dvd :
      (3 : ℤ)^1 ∣ ((2 : ℤ)^d - 1) := by
    exact dvd_trans (pow_dvd_pow (3 : ℤ) (by omega : 1 ≤ q)) h_dvd

  simpa using even_of_three_dvd_two_pow_sub_one d h_three_dvd
#check lemma_1G_even_deviation_of_positive_deficit
#print axioms lemma_1G_even_deviation_of_positive_deficit
/--
Mathlib LTE invocation for the Collatz lift factor.

For even positive `d`, the 3-adic valuation of `2^d - 1` is
`1 + v₃(d / 2)`.
-/
lemma padic_val_three_of_even_pow
  (d : ℕ) (h_even : Even d) (hd_pos : 0 < d) :
  padicValNat 3 (2^d - 1) = 1 + padicValNat 3 (d / 2) := by

  rcases h_even with ⟨k, hk⟩

  have h_d_eq : d = 2 * k := by omega
  have hd_half : d / 2 = k := by omega

  rw [hd_half]

  have h_pow_sub : 2^d - 1 = 4^k - 1^k := by
    rw [h_d_eq, pow_mul]
    have h_four : 2^2 = 4 := by norm_num
    rw [h_four]
    simp

  rw [h_pow_sub]

  have h_lte :
      padicValNat 3 (4^k - 1^k) =
        padicValNat 3 (4 - 1) + padicValNat 3 k := by
    apply padicValNat.pow_sub_pow
    · norm_num
    · norm_num
    · norm_num
    · intro h
      rcases h with ⟨c, hc⟩
      omega
    · omega

  rw [h_lte]

  have h_base : padicValNat 3 (4 - 1) = 1 := by
    norm_num

  rw [h_base]
#check padic_val_three_of_even_pow
#print axioms padic_val_three_of_even_pow
/--
Step 2: LTE substitution.

If the total valuation reaches `p`, then the half-deviation must carry
the residual valuation `p + k - n`.
-/
theorem lemma_1G_step2_lte_substitution
  (n p k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_total_val : n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p)
  (h_dk_even : Even d_k)
  (h_dk_pos : 0 < d_k) :
  padicValNat 3 (d_k / 2) ≥ p + k - n := by

  have h_LTE := padic_val_three_of_even_pow d_k h_dk_even h_dk_pos
  rw [h_LTE] at h_total_val
  omega
#check lemma_1G_step2_lte_substitution
#print axioms lemma_1G_step2_lte_substitution
/--
Step 3: Minimum deviation from divisibility of the half-deviation.
-/
theorem lemma_1G_step3_minimum_deviation
  (n p k d_k : ℕ)
  (h_pos : 0 < d_k / 2)
  (h_divisibility : 3 ^ (p + k - n) ∣ d_k / 2)
  (h_even : Even d_k) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  rcases h_divisibility with ⟨c, hc⟩

  have h_c_pos : 0 < c := by
    cases c with
    | zero => omega
    | succ c' => omega

  have h_half_bound : d_k / 2 ≥ 3 ^ (p + k - n) := by
    calc
      d_k / 2 = 3 ^ (p + k - n) * c := hc
      _ ≥ 3 ^ (p + k - n) * 1 :=
          Nat.mul_le_mul_left (3 ^ (p + k - n)) h_c_pos
      _ = 3 ^ (p + k - n) := by ring

  have h_dk_eq : d_k = 2 * (d_k / 2) := by
    rcases h_even with ⟨m, hm⟩
    omega

  omega
#check lemma_1G_step3_minimum_deviation
#print axioms lemma_1G_step3_minimum_deviation
/--
Quantitative 1G lift.

This is the intended output of Lemma 1G: once a term's lift factor reaches
the required 3-adic valuation, Mathlib LTE forces the minimum deviation size.
-/
theorem lemma_1G_quantitative_lte_lift
  (n p k d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (h_total_val : n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p)
  (h_dk_even : Even d_k)
  (h_dk_pos : 0 < d_k) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  have h_half_pos : 0 < d_k / 2 := by
    rcases h_dk_even with ⟨m, hm⟩
    omega

  have h_padic :
      padicValNat 3 (d_k / 2) ≥ p + k - n :=
    lemma_1G_step2_lte_substitution
      n p k d_k hn h_k_upper h_total_val h_dk_even h_dk_pos

  have h_half_ne : d_k / 2 ≠ 0 :=
    Nat.ne_of_gt h_half_pos

  have h_divisibility : 3 ^ (p + k - n) ∣ d_k / 2 :=
    (pow_dvd_iff_le_padicValNat
      (by norm_num : 3 ≠ 1) h_half_ne).mpr h_padic

  exact
    lemma_1G_step3_minimum_deviation
      n p k d_k h_half_pos h_divisibility h_dk_even
#check lemma_1G_quantitative_lte_lift
#print axioms lemma_1G_quantitative_lte_lift
/--
Boundary verification: entry term.

At `k = n - p`, the minimum lift is `d_k = 2`.
-/
lemma lemma_1G_step4_boundary_entry_term
  (n p k d_k : ℕ)
  (h_p_le_n : p ≤ n)
  (h_k_entry : k = n - p)
  (h_formula : d_k = 2 * 3 ^ (p + k - n)) :
  d_k = 2 := by

  have h_exponent : p + k - n = 0 := by omega
  rw [h_exponent] at h_formula
  norm_num at h_formula
  exact h_formula
#check lemma_1G_step4_boundary_entry_term
#print axioms lemma_1G_step4_boundary_entry_term
/--
Boundary verification: final internal term.

At `k = n - 2`, the minimum lift is `d_k = 2 * 3^(p - 2)`.
-/
lemma lemma_1G_step4_boundary_final_term
  (n p k d_k : ℕ)
  (h_p_ge_2 : 2 ≤ p)
  (h_n_ge_2 : 2 ≤ n)
  (h_k_final : k = n - 2)
  (h_formula : d_k = 2 * 3 ^ (p + k - n)) :
  d_k = 2 * 3 ^ (p - 2) := by

  have h_exponent : p + k - n = p - 2 := by omega
  rw [h_exponent] at h_formula
  exact h_formula
/--
A positive power of two minus one is nonzero.
-/
lemma two_pow_sub_one_ne_zero_of_pos
  (d : ℕ) (hd : 0 < d) :
  2^d - 1 ≠ 0 := by

  have h_two_le : 2 ≤ 2^d := by
    cases d with
    | zero =>
        omega
    | succ e =>
        rw [pow_succ]
        have h_pos : 0 < 2^e := pow_pos (by decide : 0 < 2) e
        calc
          2 = 1 * 2 := by ring
          _ ≤ 2^e * 2 := Nat.mul_le_mul_right 2 (Nat.succ_le_of_lt h_pos)

  omega

/--
Integer divisibility of the lift factor gives the corresponding natural
`padicValNat` lower bound, once the deviation is positive.
-/
lemma padicValNat_three_two_pow_sub_one_ge_of_int_dvd
  (q d : ℕ)
  (hd : 0 < d)
  (h_dvd : (3 : ℤ)^q ∣ (2 : ℤ)^d - 1) :
  q ≤ padicValNat 3 (2^d - 1) := by

  have h_pow_cast : ((3^q : ℕ) : ℤ) = (3 : ℤ)^q := by
    norm_num

  have h_pow_abs : ((3 : ℤ)^q).natAbs = 3^q := by
    rw [← h_pow_cast]
    simp

  have h_abs_dvd :
      3^q ∣ ((2 : ℤ)^d - 1).natAbs := by
    rcases h_dvd with ⟨c, hc⟩
    use c.natAbs
    calc
      ((2 : ℤ)^d - 1).natAbs
          = (((3 : ℤ)^q) * c).natAbs := by rw [hc]
      _ = ((3 : ℤ)^q).natAbs * c.natAbs := by
          rw [Int.natAbs_mul]
      _ = 3^q * c.natAbs := by rw [h_pow_abs]

  have h_pow_pos_nat : 0 < 2^d := pow_pos (by decide : 0 < 2) d
  have h_pow_ge_one_nat : 1 ≤ 2^d := Nat.succ_le_of_lt h_pow_pos_nat

  have h_abs_eq :
      ((2 : ℤ)^d - 1).natAbs = 2^d - 1 := by
    have h_nonneg : 0 ≤ (2 : ℤ)^d - 1 := by
      have h_cast_ge : (1 : ℤ) ≤ (2 : ℤ)^d := by
        exact_mod_cast h_pow_ge_one_nat
      linarith

    have h_cast :
        (((2 : ℤ)^d - 1).natAbs : ℤ) =
          ((2^d - 1 : ℕ) : ℤ) := by
      have h_left :
          (((2 : ℤ)^d - 1).natAbs : ℤ) =
            (2 : ℤ)^d - 1 := by
        omega

      have h_right :
          ((2^d - 1 : ℕ) : ℤ) =
            (2 : ℤ)^d - 1 := by
        rw [Nat.cast_sub h_pow_ge_one_nat]
        push_cast
        ring

      rw [h_left, h_right]

    exact_mod_cast h_cast

  have h_nat_dvd : 3^q ∣ 2^d - 1 := by
    rwa [h_abs_eq] at h_abs_dvd

  have h_nat_ne : 2^d - 1 ≠ 0 :=
    two_pow_sub_one_ne_zero_of_pos d hd

  exact
    (pow_dvd_iff_le_padicValNat
      (by norm_num : 3 ≠ 1) h_nat_ne).mp h_nat_dvd

/--
Internal-term version of the deficit-isolation step.
-/
theorem lemma_1G_internal_term_deficit
  (n x k p d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k) :
  (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) := by

  unfold T_seq at h_term_reaches

  exact
    lemma_1G_step1_valuation_deficit
      n k p (S k x) d_k hk_bound hS h_term_reaches

/--
A nonzero internal term in nonnegative-deviation form has positive deviation.
-/
lemma lemma_1G_positive_deviation_of_nonzero_internal_term
  (n x k d_k : ℕ)
  (hS : S k x = 2 * k + d_k)
  (h_nonzero : T_seq n x k ≠ 0) :
  0 < d_k := by

  by_contra h_not_pos

  have hd_zero : d_k = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_not_gt h_not_pos)

  subst d_k

  have h_factor :
      T_seq n x k =
        (3 : ℤ)^(n - 1 - k) *
          (2 : ℤ)^(2 * k) *
            ((2 : ℤ)^0 - 1) := by
    exact T_seq_factor_of_prefix_deviation n x k 0 hS

  have h_zero : T_seq n x k = 0 := by
    rw [h_factor]
    norm_num

  exact h_nonzero h_zero

/--
If a nonzero internal term has positive valuation deficit, its deviation is
even and positive.
-/
theorem lemma_1G_internal_term_even_positive_of_positive_deficit
  (n x k p d_k : ℕ)
  (hk_bound : n - 1 - k ≤ p)
  (h_deficit_pos : 0 < p - (n - 1 - k))
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k)
  (h_term_nonzero : T_seq n x k ≠ 0) :
  Even d_k ∧ 0 < d_k := by

  have h_lift_dvd :
      (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) :=
    lemma_1G_internal_term_deficit
      n x k p d_k hk_bound hS h_term_reaches

  have h_even : Even d_k :=
    lemma_1G_even_deviation_of_positive_deficit
      (p - (n - 1 - k)) d_k h_deficit_pos h_lift_dvd

  have h_pos : 0 < d_k :=
    lemma_1G_positive_deviation_of_nonzero_internal_term
      n x k d_k hS h_term_nonzero

  exact ⟨h_even, h_pos⟩

/--
Actual internal-term form of the quantitative LTE lift.
-/
theorem lemma_1G_internal_term_quantitative_lift
  (n x k p d_k : ℕ)
  (hn : 2 ≤ n)
  (h_k_upper : k ≤ n - 2)
  (hk_bound : n - 1 - k ≤ p)
  (h_deficit_pos : 0 < p - (n - 1 - k))
  (hS : S k x = 2 * k + d_k)
  (h_term_reaches : (3 : ℤ)^p ∣ T_seq n x k)
  (h_term_nonzero : T_seq n x k ≠ 0) :
  d_k ≥ 2 * 3 ^ (p + k - n) := by

  have h_lift_dvd :
      (3 : ℤ)^(p - (n - 1 - k)) ∣ ((2 : ℤ)^d_k - 1) :=
    lemma_1G_internal_term_deficit
      n x k p d_k hk_bound hS h_term_reaches

  have h_even_pos :
      Even d_k ∧ 0 < d_k :=
    lemma_1G_internal_term_even_positive_of_positive_deficit
      n x k p d_k hk_bound h_deficit_pos hS
      h_term_reaches h_term_nonzero

  rcases h_even_pos with ⟨h_even, h_pos⟩

  have h_val_ge :
      p - (n - 1 - k) ≤ padicValNat 3 (2^d_k - 1) :=
    padicValNat_three_two_pow_sub_one_ge_of_int_dvd
      (p - (n - 1 - k)) d_k h_pos h_lift_dvd

  have h_total_val :
      n - 1 - k + padicValNat 3 (2 ^ d_k - 1) ≥ p := by
    omega

  exact
    lemma_1G_quantitative_lte_lift
      n p k d_k hn h_k_upper h_total_val h_even h_pos

end Section19_Lemma1G_Quantitative_LTE
#check lemma_1G_step4_boundary_final_term
#print axioms lemma_1G_step4_boundary_final_term

-- ===============================================================
-- SECTION 20: LEMMA 1H (PERMISSIBLE 3-ADIC TRAJECTORIES)
-- ===============================================================
section Section20_Lemma1H_Permissible_Trajectories

/--
The full bifurcated LHS component range.

It represents the component chain

  T_1 + T_2 + ... + T_{n-2} + T_last.

In the existing Lean indexing, this is `Ico 1 n`, where `k = n - 1`
is interpreted by `bifurcated_component` as `T_last`.
-/
def lhs_component_range (n : ℕ) : Finset ℕ :=
  Ico 1 n

/--
A value reaches a requested 3-adic level.
-/
def reaches_three_level (level : ℕ) (z : ℤ) : Prop :=
  (3 : ℤ)^level ∣ z

/--
A bifurcated LHS component reaches a requested 3-adic level.
-/
def lhs_component_reaches_level (n x level k : ℕ) : Prop :=
  reaches_three_level level (bifurcated_component n x k)

/--
A bifurcated LHS component is active when it contributes nonzero mass.
-/
def lhs_component_active (n x k : ℕ) : Prop :=
  bifurcated_component n x k ≠ 0

/--
Backward suffix sum of the bifurcated LHS component chain.

`lhs_suffix_sum n x k` is the sum of all components from index `k`
through `T_last`.
-/
noncomputable def lhs_suffix_sum (n x k : ℕ) : ℤ :=
  ∑ i ∈ Ico k n, bifurcated_component n x i

/--
The internal-deviation parity condition.

This applies only to genuine internal terms, not to `T_last`.
-/
def internal_lift_even_deviation (k x : ℕ) : Prop :=
  (S_prime k x : ZMod 2) = 0

/--
Mechanism 1: independent global lift.

Every active bifurcated LHS component independently reaches the global target.
If an internal component needs lift beyond its positional 3-power, it is
recorded as an even-deviation lifted term.
-/
def mechanism_1_direct_lift (n x target : ℕ) : Prop :=
  ∀ k ∈ lhs_component_range n,
    lhs_component_active n x k →
      lhs_component_reaches_level n x target k ∧
        (k < n - 1 →
          n - 1 - k < target →
            internal_lift_even_deviation k x)

end Section20_Lemma1H_Permissible_Trajectories

#check lhs_component_range
#check reaches_three_level
#check lhs_component_reaches_level
#check lhs_component_active
#check lhs_suffix_sum
#check internal_lift_even_deviation
#check mechanism_1_direct_lift

/--
Mechanism 1, component-level extraction.

In the direct-lift branch, every active LHS component reaches the global target.
-/
theorem mechanism_1_component_reaches_target
  (n x target k : ℕ)
  (h_m1 : mechanism_1_direct_lift n x target)
  (hk : k ∈ lhs_component_range n)
  (h_active : lhs_component_active n x k) :
  lhs_component_reaches_level n x target k := by

  exact (h_m1 k hk h_active).1

/--
Mechanism 1, internal even-deviation extraction.

If an active internal component lies below the target by positional valuation,
then its lift occurs in the even-deviation regime.
-/
theorem mechanism_1_internal_even_deviation
  (n x target k : ℕ)
  (h_m1 : mechanism_1_direct_lift n x target)
  (hk : k ∈ lhs_component_range n)
  (h_active : lhs_component_active n x k)
  (hk_internal : k < n - 1)
  (h_below : n - 1 - k < target) :
  internal_lift_even_deviation k x := by

  exact (h_m1 k hk h_active).2 hk_internal h_below

#check mechanism_1_component_reaches_target
#check mechanism_1_internal_even_deviation
#print axioms mechanism_1_component_reaches_target
#print axioms mechanism_1_internal_even_deviation

/--
Mechanism 1, cycle-target parity mapping.

For the cycle target, every active internal component lies below the target by
positional valuation. Hence every such internal component must be in the
even-deviation lifting regime.
-/
theorem mechanism_1_cycle_target_internal_even_deviation
  (n x k : ℕ)
  (h_m1 : mechanism_1_direct_lift n x (cycle_seed_target n x))
  (hk : k ∈ lhs_component_range n)
  (h_active : lhs_component_active n x k)
  (hk_internal : k < n - 1) :
  internal_lift_even_deviation k x := by

  have h_below : n - 1 - k < cycle_seed_target n x := by
    unfold cycle_seed_target
    unfold lhs_component_range at hk
    have hk_ge : 1 ≤ k := (mem_Ico.mp hk).1
    omega

  exact
    mechanism_1_internal_even_deviation
      n x (cycle_seed_target n x) k h_m1 hk h_active
      hk_internal h_below

#check mechanism_1_cycle_target_internal_even_deviation
#print axioms mechanism_1_cycle_target_internal_even_deviation

/--
Lemma 1H, no-skipped-component principle.

This is the direct 1H invocation of Lemma 1F: in a nontrivial cycle, if the
rest of the bifurcated LHS reaches a target level not exceeding the
cycle-forced target, then the selected component cannot be skipped at that
level.
-/
theorem lemma_1H_no_skipped_component
  (n x j target : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_rest :
    reaches_three_level target
      (bifurcated_LHS n x - bifurcated_component n x j)) :
  lhs_component_reaches_level n x target j := by

  unfold lhs_component_reaches_level
  unfold reaches_three_level at h_rest ⊢

  by_contra h_skipped

  exact
    lemma_1F_step3_sovereign_cancellation
      n x j target
      h_cycle hn hx
      h_target_le
      h_skipped
      h_rest

#check lemma_1H_no_skipped_component
#print axioms lemma_1H_no_skipped_component

/--
Lemma 1H, direct-lift branch split.

Either the Mechanism-1 direct-lift condition already holds, or there is an
active component witnessing the failure of direct lifting: either it does not
reach the target level, or it is an internal below-target component whose
required lift is not in the even-deviation regime.
-/
theorem lemma_1H_direct_lift_or_failure
  (n x target : ℕ) :
  mechanism_1_direct_lift n x target ∨
    ∃ k,
      k ∈ lhs_component_range n ∧
        lhs_component_active n x k ∧
          (¬ lhs_component_reaches_level n x target k ∨
            (k < n - 1 ∧
              n - 1 - k < target ∧
                ¬ internal_lift_even_deviation k x)) := by

  by_cases h_m1 : mechanism_1_direct_lift n x target

  · exact Or.inl h_m1

  · right

    unfold mechanism_1_direct_lift at h_m1
    push Not at h_m1

    rcases h_m1 with ⟨k, hk, h_active, h_fail⟩

    refine ⟨k, hk, h_active, ?_⟩

    by_cases h_reaches :
      lhs_component_reaches_level n x target k

    · exact Or.inr (h_fail h_reaches)

    · exact Or.inl h_reaches

#check lemma_1H_direct_lift_or_failure
#print axioms lemma_1H_direct_lift_or_failure

/--
Lemma 1H, component failure forces rest failure.

This is the contrapositive form of `lemma_1H_no_skipped_component`.
In a nontrivial cycle, a component that fails to reach a level cannot be the
only obstruction while the rest of the bifurcated LHS already reaches that
same level.
-/
theorem lemma_1H_component_failure_forces_rest_failure
  (n x j target : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_target_le : target ≤ cycle_seed_target n x)
  (h_not_reaches :
    ¬ lhs_component_reaches_level n x target j) :
  ¬ reaches_three_level target
      (bifurcated_LHS n x - bifurcated_component n x j) := by

  intro h_rest

  have h_component :
      lhs_component_reaches_level n x target j :=
    lemma_1H_no_skipped_component
      n x j target
      h_cycle hn hx
      h_target_le
      h_rest

  exact h_not_reaches h_component

#check lemma_1H_component_failure_forces_rest_failure
#print axioms lemma_1H_component_failure_forces_rest_failure

/--
Lemma 1H, floor selector.

If an integer does not reach a target 3-adic level, then there is a highest
level below the target that it reaches, followed by a first missing level.
-/
theorem lemma_1H_exists_floor_below_target
  (target : ℕ)
  (z : ℤ)
  (h_not : ¬ reaches_three_level target z) :
  ∃ floor,
    floor < target ∧
      reaches_three_level floor z ∧
        ¬ reaches_three_level (floor + 1) z := by

  induction target with
  | zero =>
      exfalso
      apply h_not
      unfold reaches_three_level
      simp

  | succ t ih =>
      by_cases h_t : reaches_three_level t z

      · refine ⟨t, Nat.lt_succ_self t, h_t, ?_⟩
        simpa using h_not

      · rcases ih h_t with
          ⟨floor, hfloor_lt, hfloor_reaches, hfloor_next_not⟩

        exact
          ⟨floor,
            Nat.lt_trans hfloor_lt (Nat.lt_succ_self t),
            hfloor_reaches,
            hfloor_next_not⟩

/--
Lemma 1H, component floor selector.

If a bifurcated component does not reach the target level, then it has an
explicit below-target floor.
-/
theorem lemma_1H_component_failure_has_floor
  (n x target k : ℕ)
  (h_not :
    ¬ lhs_component_reaches_level n x target k) :
  ∃ floor,
    floor < target ∧
      lhs_component_reaches_level n x floor k ∧
        ¬ lhs_component_reaches_level n x (floor + 1) k := by

  unfold lhs_component_reaches_level at h_not

  rcases
    lemma_1H_exists_floor_below_target
      target
      (bifurcated_component n x k)
      h_not
    with ⟨floor, hfloor_lt, hfloor_reaches, hfloor_next_not⟩

  exact ⟨floor, hfloor_lt, hfloor_reaches, hfloor_next_not⟩

#check lemma_1H_exists_floor_below_target
#check lemma_1H_component_failure_has_floor
#print axioms lemma_1H_component_failure_has_floor

/--
Mechanism 2: hybrid cancellation-lift.

This is the branch left after Mechanism 1 direct componentwise lift fails.

There are two possible failure modes.

First, an active component does not reach the target level by its own
multiplicative/internal lift. Since the cycle forces the full bifurcated LHS
to reach the target, the missing valuation must come from additive
cancellation with the rest of the LHS.

Second, the component reaches the target, but an internal below-target lift
fails the required even-deviation condition. This records the hybrid
cancellation-lift obstruction that is handled by the later mechanism analysis.

Thus Mechanism 2 is exactly the non-direct-lift branch of the bifurcated
additive LHS.
-/
def mechanism_2_hybrid_cancellation_lift (n x target : ℕ) : Prop :=
  ∃ k,
    k ∈ lhs_component_range n ∧
      lhs_component_active n x k ∧
        ((¬ lhs_component_reaches_level n x target k ∧
            ¬ reaches_three_level target
              (bifurcated_LHS n x - bifurcated_component n x k)) ∨
          (k < n - 1 ∧
            n - 1 - k < target ∧
              ¬ internal_lift_even_deviation k x))

/--
The permissible 3-adic mechanisms from Lemma 1H.
-/
def lemma_1H_permissible_trajectory (n x target : ℕ) : Prop :=
  mechanism_1_direct_lift n x target ∨
    mechanism_2_hybrid_cancellation_lift n x target

#check mechanism_2_hybrid_cancellation_lift
#check lemma_1H_permissible_trajectory

/--
Lemma 1H, mechanism exhaustiveness.

For a nontrivial cycle, the bifurcated LHS can only follow one of the two
permissible mechanisms: either direct componentwise lift, or the additive
cancellation/lift branch forced by failure of direct lift.
-/
theorem lemma_1H_mechanisms_exhaustive
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  lemma_1H_permissible_trajectory n x (cycle_seed_target n x) := by

  have h_split :=
    lemma_1H_direct_lift_or_failure n x (cycle_seed_target n x)

  rcases h_split with h_m1 | h_fail

  · exact Or.inl h_m1

  · right

    rcases h_fail with ⟨k, hk, h_active, h_reason⟩

    refine ⟨k, hk, h_active, ?_⟩

    rcases h_reason with h_not_reaches | h_internal_fail

    · left
      exact
        ⟨h_not_reaches,
          lemma_1H_component_failure_forces_rest_failure
            n x k (cycle_seed_target n x)
            h_cycle hn hx
            (le_refl _)
            h_not_reaches⟩

    · right
      exact h_internal_fail

#check lemma_1H_mechanisms_exhaustive
#print axioms lemma_1H_mechanisms_exhaustive

/--
Lemma 1H cycle signature.

A nontrivial cycle supplies the cycle-forced target, terminal 3-adic
participation, and one permissible 3-adic mechanism.
-/
def lemma_1H_cycle_signature (n x : ℕ) : Prop :=
  bifurcated_LHS_reaches_target n x (cycle_seed_target n x) ∧
    (3 : ℤ) ∣ T_last n x ∧
      lemma_1H_permissible_trajectory n x (cycle_seed_target n x)

/--
Lemma 1H, cycle-to-signature mapping.

Once the permissible mechanism branch is identified, a nontrivial cycle maps
into the 1H signature used by the later capstone.
-/
theorem lemma_1H_cycle_maps_to_signature
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1)
  (h_mechanism :
    lemma_1H_permissible_trajectory n x (cycle_seed_target n x)) :
  lemma_1H_cycle_signature n x := by

  constructor
  · exact cycle_bifurcated_LHS_reaches_seed_target n x h_cycle hn hx

  constructor
  · exact lemma_1F_step2_T_last_divisible_by_three n x h_cycle hn

  · exact h_mechanism

#check lemma_1H_cycle_signature
#check lemma_1H_cycle_maps_to_signature
#print axioms lemma_1H_cycle_maps_to_signature

/--
Lemma 1H, cycle-forced signature.

A nontrivial cycle supplies the cycle-forced target, terminal 3-adic
participation, and one of the exhaustive permissible mechanisms.
-/
theorem lemma_1H_cycle_forces_signature
  (n x : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 1 < n)
  (hx : x > 1) :
  lemma_1H_cycle_signature n x := by

  exact
    lemma_1H_cycle_maps_to_signature
      n x h_cycle hn hx
      (lemma_1H_mechanisms_exhaustive n x h_cycle hn hx)

#check lemma_1H_cycle_forces_signature
#print axioms lemma_1H_cycle_forces_signature

-- ===============================================================
-- SECTION 21: LEMMA 1I (NO-LIFT PURE NEGATIVE BRANCH)
-- ===============================================================
section Section21_Lemma1I_No_Lift_Floor


/--
Lemma 1I no-lift core.

The no-lift pure negative branch begins with `a_1 = 1`.
In zero-indexed Lean notation this is `val ((T^[0]) x) = 1`.

The internal no-lift chain keeps `a_2` through `a_{n-2}` at the
equilibrium exponent `2`. Terminal exponents `a_{n-1}` and `a_n`
are split into cases below.

-/
def lemma_1I_no_lift_core (n x : ℕ) : Prop :=
  val ((T^[0]) x) = 1 ∧
    ∀ i ∈ Ico 1 (n - 2), val ((T^[i]) x) = 2

/-- Case I: `a_1 = 1`, `a_{n-1} = 2`, `a_n = 2`. -/
def lemma_1I_case_I_terminal_unperturbed (n x : ℕ) : Prop :=
  lemma_1I_no_lift_core n x ∧
    val ((T^[n - 2]) x) = 2 ∧
      val ((T^[n - 1]) x) = 2

/-- Case II: `a_1 = 1`, `a_{n-1} = 1`, `a_n = 2`. -/
def lemma_1I_case_II_penultimate_negative (n x : ℕ) : Prop :=
  lemma_1I_no_lift_core n x ∧
    val ((T^[n - 2]) x) = 1 ∧
      val ((T^[n - 1]) x) = 2

/-- Case III-A: `a_1 = 1`, `a_{n-1} = 2`, `a_n = 1`. -/
def lemma_1I_case_IIIA_final_negative_only (n x : ℕ) : Prop :=
  lemma_1I_no_lift_core n x ∧
    val ((T^[n - 2]) x) = 2 ∧
      val ((T^[n - 1]) x) = 1

/-- Case III-B: `a_1 = 1`, `a_{n-1} = 1`, `a_n = 1`. -/
def lemma_1I_case_IIIB_both_terminal_negative (n x : ℕ) : Prop :=
  lemma_1I_no_lift_core n x ∧
    val ((T^[n - 2]) x) = 1 ∧
      val ((T^[n - 1]) x) = 1

/-- Case I numerator: `N = 2^(2n-1) - 3^n + 2*3^(n-1)`. -/
noncomputable def lemma_1I_case_I_N (n : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^n + 2 * (3 : ℤ)^(n - 1)

/-- Case I denominator: `D = 2^(2n-1) - 3^n`. -/
noncomputable def lemma_1I_case_I_D (n : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n - 1) - (3 : ℤ)^n

/-- Case II numerator: `N = 7*4^(n-2) - 3^(n-1)`. -/
noncomputable def lemma_1I_case_II_N (n : ℕ) : ℤ :=
  7 * (4 : ℤ)^(n - 2) - (3 : ℤ)^(n - 1)

/-- Case II denominator: `D = 4^(n-1) - 3^n`. -/
noncomputable def lemma_1I_case_II_D (n : ℕ) : ℤ :=
  (4 : ℤ)^(n - 1) - (3 : ℤ)^n

/-- Case III-A numerator reuses Case I. -/
noncomputable def lemma_1I_case_IIIA_N (n : ℕ) : ℤ :=
  lemma_1I_case_I_N n

/-- Case III-A denominator: `D = 2^(2n-2) - 3^n`. -/
noncomputable def lemma_1I_case_IIIA_D (n : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n - 2) - (3 : ℤ)^n

/-- Case III-B numerator reuses Case II. -/
noncomputable def lemma_1I_case_IIIB_N (n : ℕ) : ℤ :=
  lemma_1I_case_II_N n

/-- Case III-B denominator: `D = 2^(2n-3) - 3^n`. -/
noncomputable def lemma_1I_case_IIIB_D (n : ℕ) : ℤ :=
  (2 : ℤ)^(2 * n - 3) - (3 : ℤ)^n

/-- Integral ratio candidate for Case I. -/
def lemma_1I_case_I_ratio_integral_candidate (n Z : ℕ) : Prop :=
  (Z : ℤ) * lemma_1I_case_I_D n = lemma_1I_case_I_N n

/-- Integral ratio candidate for Case II. -/
def lemma_1I_case_II_ratio_integral_candidate (n Z : ℕ) : Prop :=
  (Z : ℤ) * lemma_1I_case_II_D n = lemma_1I_case_II_N n

/-- Integral ratio candidate for Case III-A. -/
def lemma_1I_case_IIIA_ratio_integral_candidate (n Z : ℕ) : Prop :=
  (Z : ℤ) * lemma_1I_case_IIIA_D n = lemma_1I_case_IIIA_N n

/-- Integral ratio candidate for Case III-B. -/
def lemma_1I_case_IIIB_ratio_integral_candidate (n Z : ℕ) : Prop :=
  (Z : ℤ) * lemma_1I_case_IIIB_D n = lemma_1I_case_IIIB_N n

/--
Lemma 1I, Case I closure under the denominator bound.

If the Case I denominator is larger than the exposed residue
`2 * 3^(n-1)`, then no natural integer candidate `Z` can satisfy
`Z * D = N`.
-/
theorem lemma_1I_case_I_no_integer_ratio_of_denominator_bound
  (n Z : ℕ)
  (h_large :
    2 * (3 : ℤ)^(n - 1) < lemma_1I_case_I_D n)
  (hZ : lemma_1I_case_I_ratio_integral_candidate n Z) :
  False := by

  unfold lemma_1I_case_I_ratio_integral_candidate at hZ

  have h_split :
      lemma_1I_case_I_N n =
        lemma_1I_case_I_D n + 2 * (3 : ℤ)^(n - 1) := by
    unfold lemma_1I_case_I_N
    unfold lemma_1I_case_I_D
    ring

  have h_extra_pos :
      0 < 2 * (3 : ℤ)^(n - 1) := by
    positivity

  have hD_pos : 0 < lemma_1I_case_I_D n := by
    linarith

  have hD_dvd_extra :
      lemma_1I_case_I_D n ∣ 2 * (3 : ℤ)^(n - 1) := by
    use (Z : ℤ) - 1
    calc
      2 * (3 : ℤ)^(n - 1)
          =
        lemma_1I_case_I_N n - lemma_1I_case_I_D n := by
          rw [h_split]
          ring
      _ =
        (Z : ℤ) * lemma_1I_case_I_D n - lemma_1I_case_I_D n := by
          rw [← hZ]
      _ =
        lemma_1I_case_I_D n * ((Z : ℤ) - 1) := by
          ring

  rcases hD_dvd_extra with ⟨c, hc⟩

  have hc_pos : 0 < c := by
    by_contra h_not
    have hc_nonpos : c ≤ 0 := by omega
    have h_prod_nonpos :
        lemma_1I_case_I_D n * c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD_pos.le hc_nonpos
    rw [← hc] at h_prod_nonpos
    linarith

  have hD_le_extra :
      lemma_1I_case_I_D n ≤ 2 * (3 : ℤ)^(n - 1) := by
    calc
      lemma_1I_case_I_D n
          =
        lemma_1I_case_I_D n * 1 := by ring
      _ ≤
        lemma_1I_case_I_D n * c := by
          apply mul_le_mul_of_nonneg_left
          · omega
          · exact hD_pos.le
      _ =
        2 * (3 : ℤ)^(n - 1) := by
          rw [hc]

  linarith

/--
Lemma 1I, no-lift prefix exponent sum.

In the pure negative no-lift core, the prefix through any internal index
`m ≤ n - 2` has total exponent `2*m - 1`.
-/
lemma lemma_1I_no_lift_core_prefix_S
  (n x m : ℕ)
  (h_core : lemma_1I_no_lift_core n x)
  (hm_pos : 1 ≤ m)
  (hm_le : m ≤ n - 2) :
  S m x = 2 * m - 1 := by

  induction m with
  | zero =>
      omega

  | succ m ih =>
      rcases h_core with ⟨h_first, h_internal⟩

      by_cases hm0 : m = 0

      · subst m
        rw [S, h_first]
        simp [S]

      · have hm_pos' : 1 ≤ m :=
          Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)

        have hm_le' : m ≤ n - 2 := by
          omega

        have hS_m :
            S m x = 2 * m - 1 :=
          ih hm_pos' hm_le'

        have hm_mem : m ∈ Ico 1 (n - 2) := by
          rw [mem_Ico]
          exact ⟨hm_pos', by omega⟩

        have hval :
            val ((T^[m]) x) = 2 :=
          h_internal m hm_mem

        rw [S, hS_m, hval]
        omega
/--
Lemma 1I, numerator recurrence for `sum_T`.

This is the geometric numerator recurrence
`N_{n+1} = 3 N_n + 2^{S_n}` in integer form.
-/
lemma lemma_1I_sum_T_succ_int
  (n x : ℕ) :
  (sum_T (n + 1) x : ℤ) =
    3 * (sum_T n x : ℤ) + (2 : ℤ)^(S n x) := by

  rw [← closed_numerator_eq_sum_T (n + 1) x]
  rw [← closed_numerator_eq_sum_T n x]
  simp [closed_numerator]

/--
Lemma 1I, no-lift core predecessor.

The no-lift core at length `n` restricts to the no-lift core at length `n - 1`.
-/
lemma lemma_1I_no_lift_core_prev
  (n x : ℕ)
  (hn : 6 ≤ n)
  (h_core : lemma_1I_no_lift_core n x) :
  lemma_1I_no_lift_core (n - 1) x := by

  rcases h_core with ⟨h_first, h_internal⟩

  refine ⟨h_first, ?_⟩

  intro i hi

  have hi_big : i ∈ Ico 1 (n - 2) := by
    rw [mem_Ico] at hi ⊢
    omega

  exact h_internal i hi_big

/--
Lemma 1I, first-visible terminal prefix.

If the numerator-visible terminal exponent is unperturbed, then
`S_{n-1} = 2(n-1)-1`.
-/
lemma lemma_1I_first_visible_S_pred
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_core : lemma_1I_no_lift_core n x)
  (h_pen : val ((T^[n - 2]) x) = 2) :
  S (n - 1) x = 2 * (n - 1) - 1 := by

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  rw [h_step, h_prefix, h_pen]
  omega

/--
Lemma 1I, second-visible terminal prefix.

If the numerator-visible terminal exponent is negative, then
`S_{n-1} = 2n - 4`.
-/
lemma lemma_1I_second_visible_S_pred
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_core : lemma_1I_no_lift_core n x)
  (h_pen : val ((T^[n - 2]) x) = 1) :
  S (n - 1) x = 2 * n - 4 := by

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  rw [h_step, h_prefix, h_pen]
  omega

/--
Lemma 1I, first visible numerator evaluation.

This covers Case I and Case III-A, since `a_n` is invisible to the numerator.
-/
theorem lemma_1I_first_visible_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_core : lemma_1I_no_lift_core n x)
  (h_pen : val ((T^[n - 2]) x) = 2) :
  (sum_T n x : ℤ) = lemma_1I_case_I_N n := by

  induction n using Nat.strong_induction_on with
  | h n ih =>

      by_cases h_base : n = 5

      · subst n

        have hS0 : S 0 x = 0 := by
          simp [S]

        have hS1 : S 1 x = 1 := by
          have h :=
            lemma_1I_no_lift_core_prefix_S 5 x 1
              h_core (by omega) (by omega)
          simpa using h

        have hS2 : S 2 x = 3 := by
          have h :=
            lemma_1I_no_lift_core_prefix_S 5 x 2
              h_core (by omega) (by omega)
          norm_num at h
          exact h

        have hS3 : S 3 x = 5 := by
          have h :=
            lemma_1I_no_lift_core_prefix_S 5 x 3
              h_core (by omega) (by omega)
          norm_num at h
          exact h

        have hS4 : S 4 x = 7 := by
          have h_step :
              S 4 x = S 3 x + val ((T^[3]) x) := by
            rw [S]

          have h_pen3 :
              val ((T^[3]) x) = 2 := by
            norm_num at h_pen
            exact h_pen

          rw [h_step, hS3, h_pen3]

        unfold sum_T
        unfold lemma_1I_case_I_N

        simp only [sum_range_succ, sum_range_zero, hS0, hS1, hS2, hS3, hS4]
        norm_num

      · have hn_ge_six : 6 ≤ n := by
          omega

        have h_core_prev :
            lemma_1I_no_lift_core (n - 1) x :=
          lemma_1I_no_lift_core_prev n x hn_ge_six h_core

        have h_pen_prev :
            val ((T^[(n - 1) - 2]) x) = 2 := by
          have h_idx :
              (n - 1) - 2 = n - 3 := by
            omega

          rw [h_idx]

          rcases h_core with ⟨_, h_internal⟩

          have h_mem : n - 3 ∈ Ico 1 (n - 2) := by
            rw [mem_Ico]
            omega

          exact h_internal (n - 3) h_mem

        have h_prev_sum :
            (sum_T (n - 1) x : ℤ) =
              lemma_1I_case_I_N (n - 1) :=
          ih (n - 1) (by omega) (by omega) h_core_prev h_pen_prev

        have h_pred_S :
            S (n - 1) x = 2 * (n - 1) - 1 :=
          lemma_1I_first_visible_S_pred n x hn h_core h_pen

        have h_rec :
            (sum_T n x : ℤ) =
              3 * (sum_T (n - 1) x : ℤ) +
                (2 : ℤ)^(S (n - 1) x) := by
          have h :=
            lemma_1I_sum_T_succ_int (n - 1) x
          have h_succ : n - 1 + 1 = n := by omega
          rwa [h_succ] at h

        rw [h_rec, h_prev_sum, h_pred_S]

        unfold lemma_1I_case_I_N

        have h_two_pow :
            (2 : ℤ)^(2 * n - 1) =
              4 * (2 : ℤ)^(2 * (n - 1) - 1) := by
          have h_exp :
              2 * n - 1 = (2 * (n - 1) - 1) + 2 := by
            omega
          rw [h_exp, pow_add]
          norm_num
          ring

        have h_three_pow_n :
            (3 : ℤ)^n =
              3 * (3 : ℤ)^(n - 1) := by
          have h_exp :
              n = (n - 1) + 1 := by
            omega
          rw [h_exp, pow_add]
          norm_num
          ring

        have h_three_pow_prev :
            (3 : ℤ)^(n - 1) =
              3 * (3 : ℤ)^((n - 1) - 1) := by
          have h_exp :
              n - 1 = ((n - 1) - 1) + 1 := by
            omega
          rw [h_exp, pow_add]
          norm_num
          ring

        rw [h_two_pow, h_three_pow_n, h_three_pow_prev]
        ring

/--
Lemma 1I, second visible numerator evaluation.

This covers Case II and Case III-B, since `a_n` is invisible to the numerator.
-/
theorem lemma_1I_second_visible_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_core : lemma_1I_no_lift_core n x)
  (h_pen : val ((T^[n - 2]) x) = 1) :
  (sum_T n x : ℤ) = lemma_1I_case_II_N n := by

  by_cases h_base : n = 5

  · subst n

    have hS0 : S 0 x = 0 := by
      simp [S]

    have hS1 : S 1 x = 1 := by
      have h :=
        lemma_1I_no_lift_core_prefix_S 5 x 1
          h_core (by omega) (by omega)
      simpa using h

    have hS2 : S 2 x = 3 := by
      have h :=
        lemma_1I_no_lift_core_prefix_S 5 x 2
          h_core (by omega) (by omega)
      norm_num at h
      exact h

    have hS3 : S 3 x = 5 := by
      have h :=
        lemma_1I_no_lift_core_prefix_S 5 x 3
          h_core (by omega) (by omega)
      norm_num at h
      exact h

    have hS4 : S 4 x = 6 := by
      have h_step :
          S 4 x = S 3 x + val ((T^[3]) x) := by
        rw [S]

      have h_pen3 :
          val ((T^[3]) x) = 1 := by
        norm_num at h_pen
        exact h_pen

      rw [h_step, hS3, h_pen3]

    unfold sum_T
    unfold lemma_1I_case_II_N

    simp only [sum_range_succ, sum_range_zero, hS0, hS1, hS2, hS3, hS4]
    norm_num

  · have hn_ge_six : 6 ≤ n := by
      omega

    have h_core_prev :
        lemma_1I_no_lift_core (n - 1) x :=
      lemma_1I_no_lift_core_prev n x hn_ge_six h_core

    have h_pen_prev :
        val ((T^[(n - 1) - 2]) x) = 2 := by
      have h_idx :
          (n - 1) - 2 = n - 3 := by
        omega

      rw [h_idx]

      rcases h_core with ⟨_, h_internal⟩

      have h_mem : n - 3 ∈ Ico 1 (n - 2) := by
        rw [mem_Ico]
        omega

      exact h_internal (n - 3) h_mem

    have h_prev_sum :
        (sum_T (n - 1) x : ℤ) =
          lemma_1I_case_I_N (n - 1) :=
      lemma_1I_first_visible_sum_eval
        (n - 1) x (by omega) h_core_prev h_pen_prev

    have h_pred_S :
        S (n - 1) x = 2 * n - 4 :=
      lemma_1I_second_visible_S_pred n x hn h_core h_pen

    have h_rec :
        (sum_T n x : ℤ) =
          3 * (sum_T (n - 1) x : ℤ) +
            (2 : ℤ)^(S (n - 1) x) := by
      have h :=
        lemma_1I_sum_T_succ_int (n - 1) x
      have h_succ : n - 1 + 1 = n := by omega
      rwa [h_succ] at h

    rw [h_rec, h_prev_sum, h_pred_S]

    unfold lemma_1I_case_I_N
    unfold lemma_1I_case_II_N

    have h_two_prev :
        (2 : ℤ)^(2 * (n - 1) - 1) =
          2 * (2 : ℤ)^(2 * n - 4) := by
      have h_exp :
          2 * (n - 1) - 1 = (2 * n - 4) + 1 := by
        omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_three_prev_prev :
        (3 : ℤ)^((n - 1) - 1) =
          (3 : ℤ)^(n - 2) := by
      have h_exp : (n - 1) - 1 = n - 2 := by
        omega
      rw [h_exp]

    have h_three_prev :
        (3 : ℤ)^(n - 1) =
          3 * (3 : ℤ)^(n - 2) := by
      have h_exp :
          n - 1 = (n - 2) + 1 := by
        omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_four :
        (4 : ℤ)^(n - 2) =
          (2 : ℤ)^(2 * n - 4) := by
      have h_exp :
          2 * n - 4 = 2 * (n - 2) := by
        omega
      rw [h_exp, pow_mul]
      norm_num

    rw [h_two_prev, h_three_prev_prev, h_three_prev, h_four]
    ring

/--
Lemma 1I, Case I numerator evaluation.
-/
theorem lemma_1I_case_I_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_I_terminal_unperturbed n x) :
  (sum_T n x : ℤ) = lemma_1I_case_I_N n := by

  exact
    lemma_1I_first_visible_sum_eval
      n x hn h_case.1 h_case.2.1

/--
Lemma 1I, Case II numerator evaluation.
-/
theorem lemma_1I_case_II_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_II_penultimate_negative n x) :
  (sum_T n x : ℤ) = lemma_1I_case_II_N n := by

  exact
    lemma_1I_second_visible_sum_eval
      n x hn h_case.1 h_case.2.1

/--
Lemma 1I, Case III-A numerator evaluation.

The final exponent `a_n` is invisible to the numerator, so this reuses the
first-visible numerator evaluation.
-/
theorem lemma_1I_case_IIIA_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_IIIA_final_negative_only n x) :
  (sum_T n x : ℤ) = lemma_1I_case_IIIA_N n := by

  unfold lemma_1I_case_IIIA_N

  exact
    lemma_1I_first_visible_sum_eval
      n x hn h_case.1 h_case.2.1

/--
Lemma 1I, Case III-B numerator evaluation.

The final exponent `a_n` is invisible to the numerator, so this reuses the
second-visible numerator evaluation.
-/
theorem lemma_1I_case_IIIB_sum_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_IIIB_both_terminal_negative n x) :
  (sum_T n x : ℤ) = lemma_1I_case_IIIB_N n := by

  unfold lemma_1I_case_IIIB_N

  exact
    lemma_1I_second_visible_sum_eval
      n x hn h_case.1 h_case.2.1

#check lemma_1I_sum_T_succ_int
#check lemma_1I_no_lift_core_prev
#check lemma_1I_first_visible_S_pred
#check lemma_1I_second_visible_S_pred
#check lemma_1I_first_visible_sum_eval
#check lemma_1I_second_visible_sum_eval
#check lemma_1I_case_I_sum_eval
#check lemma_1I_case_II_sum_eval
#check lemma_1I_case_IIIA_sum_eval
#check lemma_1I_case_IIIB_sum_eval

/--
Lemma 1I, Case I total exponent evaluation.

Case I has `a_1 = 1`, `a_{n-1} = 2`, and `a_n = 2`.
-/
theorem lemma_1I_case_I_S_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_I_terminal_unperturbed n x) :
  S n x = 2 * n - 1 := by

  rcases h_case with ⟨h_core, h_pen, h_fin⟩

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step_n :
      S n x = S (n - 1) x + val ((T^[n - 1]) x) := by
    have h : n = Nat.succ (n - 1) := by omega
    rw [h]
    simp [S]

  have h_step_pen :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  calc
    S n x
        = S (n - 1) x + val ((T^[n - 1]) x) := h_step_n
    _ = (S (n - 2) x + val ((T^[n - 2]) x)) +
          val ((T^[n - 1]) x) := by
          rw [h_step_pen]
    _ = (2 * (n - 2) - 1 + 2) + 2 := by
          rw [h_prefix, h_pen, h_fin]
    _ = 2 * n - 1 := by
          omega

/--
Lemma 1I, Case II total exponent evaluation.

Case II has `a_1 = 1`, `a_{n-1} = 1`, and `a_n = 2`.
-/
theorem lemma_1I_case_II_S_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_II_penultimate_negative n x) :
  S n x = 2 * n - 2 := by

  rcases h_case with ⟨h_core, h_pen, h_fin⟩

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step_n :
      S n x = S (n - 1) x + val ((T^[n - 1]) x) := by
    have h : n = Nat.succ (n - 1) := by omega
    rw [h]
    simp [S]

  have h_step_pen :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  calc
    S n x
        = S (n - 1) x + val ((T^[n - 1]) x) := h_step_n
    _ = (S (n - 2) x + val ((T^[n - 2]) x)) +
          val ((T^[n - 1]) x) := by
          rw [h_step_pen]
    _ = (2 * (n - 2) - 1 + 1) + 2 := by
          rw [h_prefix, h_pen, h_fin]
    _ = 2 * n - 2 := by
          omega

/--
Lemma 1I, Case III-A total exponent evaluation.

Case III-A has `a_1 = 1`, `a_{n-1} = 2`, and `a_n = 1`.
-/
theorem lemma_1I_case_IIIA_S_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_IIIA_final_negative_only n x) :
  S n x = 2 * n - 2 := by

  rcases h_case with ⟨h_core, h_pen, h_fin⟩

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step_n :
      S n x = S (n - 1) x + val ((T^[n - 1]) x) := by
    have h : n = Nat.succ (n - 1) := by omega
    rw [h]
    simp [S]

  have h_step_pen :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  calc
    S n x
        = S (n - 1) x + val ((T^[n - 1]) x) := h_step_n
    _ = (S (n - 2) x + val ((T^[n - 2]) x)) +
          val ((T^[n - 1]) x) := by
          rw [h_step_pen]
    _ = (2 * (n - 2) - 1 + 2) + 1 := by
          rw [h_prefix, h_pen, h_fin]
    _ = 2 * n - 2 := by
          omega

/--
Lemma 1I, Case III-B total exponent evaluation.

Case III-B has `a_1 = 1`, `a_{n-1} = 1`, and `a_n = 1`.
-/
theorem lemma_1I_case_IIIB_S_eval
  (n x : ℕ)
  (hn : 5 ≤ n)
  (h_case : lemma_1I_case_IIIB_both_terminal_negative n x) :
  S n x = 2 * n - 3 := by

  rcases h_case with ⟨h_core, h_pen, h_fin⟩

  have h_prefix :
      S (n - 2) x = 2 * (n - 2) - 1 :=
    lemma_1I_no_lift_core_prefix_S n x (n - 2)
      h_core (by omega) (by omega)

  have h_step_n :
      S n x = S (n - 1) x + val ((T^[n - 1]) x) := by
    have h : n = Nat.succ (n - 1) := by omega
    rw [h]
    simp [S]

  have h_step_pen :
      S (n - 1) x = S (n - 2) x + val ((T^[n - 2]) x) := by
    have h : n - 1 = Nat.succ (n - 2) := by omega
    rw [h]
    simp [S]

  calc
    S n x
        = S (n - 1) x + val ((T^[n - 1]) x) := h_step_n
    _ = (S (n - 2) x + val ((T^[n - 2]) x)) +
          val ((T^[n - 1]) x) := by
          rw [h_step_pen]
    _ = (2 * (n - 2) - 1 + 1) + 1 := by
          rw [h_prefix, h_pen, h_fin]
    _ = 2 * n - 3 := by
          omega

#check lemma_1I_no_lift_core_prefix_S
#check lemma_1I_case_I_S_eval
#check lemma_1I_case_II_S_eval
#check lemma_1I_case_IIIA_S_eval
#check lemma_1I_case_IIIB_S_eval
/--
Case I exponential bound.

For `n ≥ 5`, the power of two dominates the exposed Case I obstruction.
-/
lemma lemma_1I_case_I_five_mul_three_pow_lt_two_pow
  (n : ℕ)
  (hn : 5 ≤ n) :
  5 * 3^(n - 1) < 2^(2 * n - 1) := by

  have h_core : ∀ t : ℕ, 405 * 3^t < 512 * 4^t := by
    intro t
    induction t with
    | zero =>
        norm_num
    | succ t ih =>
        calc
          405 * 3^(t + 1)
              = 3 * (405 * 3^t) := by ring
          _ < 3 * (512 * 4^t) := by
              exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 4 * (512 * 4^t) := by
              exact Nat.mul_le_mul_right (512 * 4^t) (by norm_num : 3 ≤ 4)
          _ = 512 * 4^(t + 1) := by ring

  let t := n - 5

  have hn_eq : n = t + 5 := by
    dsimp [t]
    omega

  rw [hn_eq]

  have h_left :
      5 * 3^(t + 5 - 1) = 405 * 3^t := by
    have h_exp : t + 5 - 1 = t + 4 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  have h_right :
      2^(2 * (t + 5) - 1) = 512 * 4^t := by
    have h_exp : 2 * (t + 5) - 1 = 2 * t + 9 := by omega
    rw [h_exp, pow_add]

    have h_two :
        2^(2 * t) = 4^t := by
      rw [pow_mul]
      norm_num

    rw [h_two]
    norm_num
    ring

  rw [h_left, h_right]

  exact h_core t

/--
Case I denominator bound.
-/
theorem lemma_1I_case_I_denominator_bound
  (n : ℕ)
  (hn : 5 ≤ n) :
  2 * (3 : ℤ)^(n - 1) < lemma_1I_case_I_D n := by

  unfold lemma_1I_case_I_D

  have h_bound_nat :
      5 * 3^(n - 1) < 2^(2 * n - 1) :=
    lemma_1I_case_I_five_mul_three_pow_lt_two_pow n hn

  have h_bound_int :
      5 * (3 : ℤ)^(n - 1) < (2 : ℤ)^(2 * n - 1) := by
    exact_mod_cast h_bound_nat

  have h_three :
      (3 : ℤ)^n = 3 * (3 : ℤ)^(n - 1) := by
    have h_exp : n = (n - 1) + 1 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_three]
  nlinarith

/--
Lemma 1I, Case I closure.

No natural integer `Z` can satisfy the Case I ratio equation.
-/
theorem lemma_1I_case_I_no_integer_ratio
  (n Z : ℕ)
  (hn : 3 ≤ n)
  (hZ : lemma_1I_case_I_ratio_integral_candidate n Z) :
  False := by

  by_cases hn_ge_five : 5 ≤ n

  · exact
      lemma_1I_case_I_no_integer_ratio_of_denominator_bound
        n Z
        (lemma_1I_case_I_denominator_bound n hn_ge_five)
        hZ

  · have hn_le_four : n ≤ 4 := by omega
    interval_cases n

    · norm_num
        [lemma_1I_case_I_ratio_integral_candidate,
         lemma_1I_case_I_N,
         lemma_1I_case_I_D] at hZ
      omega

    · norm_num
        [lemma_1I_case_I_ratio_integral_candidate,
         lemma_1I_case_I_N,
         lemma_1I_case_I_D] at hZ
      omega
/--
Case II exponential bound.

For `n ≥ 12`, the power of four dominates the exposed Case II obstruction.
-/
lemma lemma_1I_case_II_fifteen_mul_three_pow_lt_four_pow
  (n : ℕ)
  (hn : 12 ≤ n) :
  15 * 3^(n - 2) < 4^(n - 2) := by

  have h_core : ∀ t : ℕ, 885735 * 3^t < 1048576 * 4^t := by
    intro t
    induction t with
    | zero =>
        norm_num
    | succ t ih =>
        calc
          885735 * 3^(t + 1)
              = 3 * (885735 * 3^t) := by ring
          _ < 3 * (1048576 * 4^t) := by
              exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 4 * (1048576 * 4^t) := by
              exact Nat.mul_le_mul_right (1048576 * 4^t) (by norm_num : 3 ≤ 4)
          _ = 1048576 * 4^(t + 1) := by ring

  let t := n - 12

  have hn_eq : n = t + 12 := by
    dsimp [t]
    omega

  rw [hn_eq]

  have h_left :
      15 * 3^(t + 12 - 2) = 885735 * 3^t := by
    have h_exp : t + 12 - 2 = t + 10 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  have h_right :
      4^(t + 12 - 2) = 1048576 * 4^t := by
    have h_exp : t + 12 - 2 = t + 10 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_left, h_right]

  exact h_core t

/--
Lemma 1I, Case II closure.

No natural integer `Z` can satisfy the Case II ratio equation.
-/
theorem lemma_1I_case_II_no_integer_ratio
  (n Z : ℕ)
  (hn : 5 ≤ n)
  (hZ : lemma_1I_case_II_ratio_integral_candidate n Z) :
  False := by

  by_cases hn_ge_twelve : 12 ≤ n

  · unfold lemma_1I_case_II_ratio_integral_candidate at hZ

    have h_bound_nat :
        15 * 3^(n - 2) < 4^(n - 2) :=
      lemma_1I_case_II_fifteen_mul_three_pow_lt_four_pow n hn_ge_twelve

    have h_bound_int :
        15 * (3 : ℤ)^(n - 2) < (4 : ℤ)^(n - 2) := by
      exact_mod_cast h_bound_nat

    have hB_nonneg :
        0 ≤ (3 : ℤ)^(n - 2) := by
      positivity

    have hA_pos :
        0 < (4 : ℤ)^(n - 2) := by
      positivity

    have h_pow4 :
        (4 : ℤ)^(n - 1) = 4 * (4 : ℤ)^(n - 2) := by
      have h_exp : n - 1 = (n - 2) + 1 := by omega
      rw [h_exp, pow_add]
      ring

    have h_pow3_n :
        (3 : ℤ)^n = 9 * (3 : ℤ)^(n - 2) := by
      have h_exp : n = (n - 2) + 2 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_pow3_n1 :
        (3 : ℤ)^(n - 1) = 3 * (3 : ℤ)^(n - 2) := by
      have h_exp : n - 1 = (n - 2) + 1 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have hD_pos :
        0 < lemma_1I_case_II_D n := by
      unfold lemma_1I_case_II_D
      rw [h_pow4, h_pow3_n]
      nlinarith

    have hN_pos :
        0 < lemma_1I_case_II_N n := by
      unfold lemma_1I_case_II_N
      rw [h_pow3_n1]
      nlinarith

    have hN_gt_D :
        lemma_1I_case_II_D n < lemma_1I_case_II_N n := by
      unfold lemma_1I_case_II_D
      unfold lemma_1I_case_II_N
      rw [h_pow4, h_pow3_n, h_pow3_n1]
      nlinarith

    have hN_lt_twoD :
        lemma_1I_case_II_N n < 2 * lemma_1I_case_II_D n := by
      unfold lemma_1I_case_II_D
      unfold lemma_1I_case_II_N
      rw [h_pow4, h_pow3_n, h_pow3_n1]
      nlinarith

    by_cases hZ_le_one : Z ≤ 1

    · interval_cases Z

      · norm_num at hZ
        linarith

      · norm_num at hZ
        linarith

    · have hZ_ge_two_nat : 2 ≤ Z := by omega

      have hZ_ge_two_int : (2 : ℤ) ≤ (Z : ℤ) := by
        exact_mod_cast hZ_ge_two_nat

      have h_twoD_le_N :
          2 * lemma_1I_case_II_D n ≤ lemma_1I_case_II_N n := by
        calc
          2 * lemma_1I_case_II_D n
              ≤
            (Z : ℤ) * lemma_1I_case_II_D n := by
              exact mul_le_mul_of_nonneg_right hZ_ge_two_int hD_pos.le
          _ =
            lemma_1I_case_II_N n := hZ

      linarith

  · have hn_le_eleven : n ≤ 11 := by omega
    interval_cases n <;>
      norm_num
        [lemma_1I_case_II_ratio_integral_candidate,
         lemma_1I_case_II_N,
         lemma_1I_case_II_D] at hZ <;>
      omega
/--
Lemma 1I, Case III-A closure under the residue bound.

In Case III-A,
`N = 2 * D + 5 * 3^(n-1)`.
If the denominator is larger than this exposed residue, no natural integer
candidate `Z` can satisfy `Z * D = N`.
-/
theorem lemma_1I_case_IIIA_no_integer_ratio_of_residue_bound
  (n Z : ℕ)
  (hn : 1 ≤ n)
  (h_large :
    5 * (3 : ℤ)^(n - 1) < lemma_1I_case_IIIA_D n)
  (hZ : lemma_1I_case_IIIA_ratio_integral_candidate n Z) :
  False := by

  unfold lemma_1I_case_IIIA_ratio_integral_candidate at hZ

  have h_split :
      lemma_1I_case_IIIA_N n =
        2 * lemma_1I_case_IIIA_D n + 5 * (3 : ℤ)^(n - 1) := by
    unfold lemma_1I_case_IIIA_N
    unfold lemma_1I_case_IIIA_D
    unfold lemma_1I_case_I_N

    have h_pow2 :
        (2 : ℤ)^(2 * n - 1) =
          2 * (2 : ℤ)^(2 * n - 2) := by
      have h_exp : 2 * n - 1 = (2 * n - 2) + 1 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_pow3 :
        (3 : ℤ)^n =
          3 * (3 : ℤ)^(n - 1) := by
      have h_exp : n = (n - 1) + 1 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    rw [h_pow2, h_pow3]
    ring

  have h_residue_pos :
      0 < 5 * (3 : ℤ)^(n - 1) := by
    positivity

  have hD_pos : 0 < lemma_1I_case_IIIA_D n := by
    linarith

  have hD_dvd_residue :
      lemma_1I_case_IIIA_D n ∣ 5 * (3 : ℤ)^(n - 1) := by
    use (Z : ℤ) - 2
    calc
      5 * (3 : ℤ)^(n - 1)
          =
        lemma_1I_case_IIIA_N n - 2 * lemma_1I_case_IIIA_D n := by
          rw [h_split]
          ring
      _ =
        (Z : ℤ) * lemma_1I_case_IIIA_D n -
          2 * lemma_1I_case_IIIA_D n := by
          rw [← hZ]
      _ =
        lemma_1I_case_IIIA_D n * ((Z : ℤ) - 2) := by
          ring

  rcases hD_dvd_residue with ⟨c, hc⟩

  have hc_pos : 0 < c := by
    by_contra h_not
    have hc_nonpos : c ≤ 0 := by omega
    have h_prod_nonpos :
        lemma_1I_case_IIIA_D n * c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD_pos.le hc_nonpos
    rw [← hc] at h_prod_nonpos
    linarith

  have hD_le_residue :
      lemma_1I_case_IIIA_D n ≤ 5 * (3 : ℤ)^(n - 1) := by
    calc
      lemma_1I_case_IIIA_D n
          =
        lemma_1I_case_IIIA_D n * 1 := by ring
      _ ≤
        lemma_1I_case_IIIA_D n * c := by
          apply mul_le_mul_of_nonneg_left
          · omega
          · exact hD_pos.le
      _ =
        5 * (3 : ℤ)^(n - 1) := by
          rw [hc]

  linarith

/--
Case III-A residue bound.

For `n ≥ 9`, the Case III-A denominator is larger than the exposed residue
`5 * 3^(n-1)`.
-/
theorem lemma_1I_case_IIIA_residue_bound
  (n : ℕ)
  (hn : 9 ≤ n) :
  5 * (3 : ℤ)^(n - 1) < lemma_1I_case_IIIA_D n := by

  unfold lemma_1I_case_IIIA_D

  have h_core : ∀ t : ℕ, 52488 * 3^t < 65536 * 4^t := by
    intro t
    induction t with
    | zero =>
        norm_num
    | succ t ih =>
        calc
          52488 * 3^(t + 1)
              = 3 * (52488 * 3^t) := by ring
          _ < 3 * (65536 * 4^t) := by
              exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 4 * (65536 * 4^t) := by
              exact Nat.mul_le_mul_right (65536 * 4^t) (by norm_num : 3 ≤ 4)
          _ = 65536 * 4^(t + 1) := by ring

  let t := n - 9

  have hn_eq : n = t + 9 := by
    dsimp [t]
    omega

  rw [hn_eq]

  have h_left_nat :
      8 * 3^(t + 9 - 1) < 4^(t + 9 - 1) := by
    have h_left :
        8 * 3^(t + 9 - 1) = 52488 * 3^t := by
      have h_exp : t + 9 - 1 = t + 8 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_right :
        4^(t + 9 - 1) = 65536 * 4^t := by
      have h_exp : t + 9 - 1 = t + 8 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    rw [h_left, h_right]
    exact h_core t

  have h_left_int :
      8 * (3 : ℤ)^(t + 9 - 1) < (4 : ℤ)^(t + 9 - 1) := by
    exact_mod_cast h_left_nat

  have h_pow2_to_four :
      (2 : ℤ)^(2 * (t + 9) - 2) =
        (4 : ℤ)^(t + 9 - 1) := by
    have h_exp : 2 * (t + 9) - 2 = 2 * (t + 9 - 1) := by omega
    rw [h_exp, pow_mul]
    norm_num

  have h_pow3 :
      (3 : ℤ)^(t + 9) =
        3 * (3 : ℤ)^(t + 9 - 1) := by
    have h_exp : t + 9 = (t + 9 - 1) + 1 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_pow2_to_four, h_pow3]
  nlinarith

/--
Lemma 1I, Case III-A closure.

No natural integer `Z` can satisfy the Case III-A ratio equation.
-/
theorem lemma_1I_case_IIIA_no_integer_ratio
  (n Z : ℕ)
  (hn : 3 ≤ n)
  (hZ : lemma_1I_case_IIIA_ratio_integral_candidate n Z) :
  False := by

  by_cases hn_ge_nine : 9 ≤ n

  · exact
      lemma_1I_case_IIIA_no_integer_ratio_of_residue_bound
        n Z
        (by omega)
        (lemma_1I_case_IIIA_residue_bound n hn_ge_nine)
        hZ

  · have hn_le_eight : n ≤ 8 := by omega
    interval_cases n <;>
      norm_num
        [lemma_1I_case_IIIA_ratio_integral_candidate,
         lemma_1I_case_IIIA_N,
         lemma_1I_case_IIIA_D,
         lemma_1I_case_I_N] at hZ <;>
      omega
/--
Lemma 1I, Case III-B closure under the residue bound.
-/
theorem lemma_1I_case_IIIB_no_integer_ratio_of_residue_bound
  (n Z : ℕ)
  (hn : 2 ≤ n)
  (h_large :
    57 * (3 : ℤ)^(n - 2) < lemma_1I_case_IIIB_D n)
  (hZ : lemma_1I_case_IIIB_ratio_integral_candidate n Z) :
  False := by

  unfold lemma_1I_case_IIIB_ratio_integral_candidate at hZ
  unfold lemma_1I_case_IIIB_N at hZ
  unfold lemma_1I_case_IIIB_D at hZ
  unfold lemma_1I_case_II_N at hZ

  unfold lemma_1I_case_IIIB_D at h_large

  have h_pow2_to_four :
      (2 : ℤ)^(2 * n - 3) =
        2 * (4 : ℤ)^(n - 2) := by
    have h_exp : 2 * n - 3 = 2 * (n - 2) + 1 := by omega
    rw [h_exp, pow_add, pow_mul]
    norm_num
    ring

  have h_pow3_n :
      (3 : ℤ)^n =
        9 * (3 : ℤ)^(n - 2) := by
    have h_exp : n = (n - 2) + 2 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  have h_pow3_n1 :
      (3 : ℤ)^(n - 1) =
        3 * (3 : ℤ)^(n - 2) := by
    have h_exp : n - 1 = (n - 2) + 1 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_pow2_to_four, h_pow3_n, h_pow3_n1] at hZ
  rw [h_pow2_to_four, h_pow3_n] at h_large

  let A : ℤ := (4 : ℤ)^(n - 2)
  let B : ℤ := (3 : ℤ)^(n - 2)
  let D : ℤ := 2 * A - 9 * B

  have hZ_D :
      (Z : ℤ) * D = 7 * A - 3 * B := by
    dsimp [D, A, B]
    exact hZ

  have h_large_D :
      57 * B < D := by
    dsimp [D, A, B]
    exact h_large

  have h_residue_pos :
      0 < 57 * B := by
    dsimp [B]
    positivity

  have hD_pos : 0 < D := by
    linarith

  have hD_dvd_residue :
      D ∣ 57 * B := by
    have hD_dvd_first :
        D ∣ A + 24 * B := by
      use (Z : ℤ) - 3
      calc
        A + 24 * B
            =
          (7 * A - 3 * B) - 3 * D := by
            dsimp [D]
            ring
        _ =
          (Z : ℤ) * D - 3 * D := by
            rw [← hZ_D]
        _ =
          D * ((Z : ℤ) - 3) := by
            ring

    have hD_dvd_second :
        D ∣ 2 * (A + 24 * B) - D := by
      exact dvd_sub (dvd_mul_of_dvd_right hD_dvd_first 2) (dvd_refl D)

    have h_residue_eq :
        2 * (A + 24 * B) - D = 57 * B := by
      dsimp [D]
      ring

    rw [h_residue_eq] at hD_dvd_second
    exact hD_dvd_second

  rcases hD_dvd_residue with ⟨c, hc⟩

  have hc_pos : 0 < c := by
    by_contra h_not
    have hc_nonpos : c ≤ 0 := by omega
    have h_prod_nonpos :
        D * c ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD_pos.le hc_nonpos
    rw [← hc] at h_prod_nonpos
    linarith

  have hD_le_residue :
      D ≤ 57 * B := by
    calc
      D
          =
        D * 1 := by ring
      _ ≤
        D * c := by
          apply mul_le_mul_of_nonneg_left
          · omega
          · exact hD_pos.le
      _ =
        57 * B := by
          rw [hc]

  linarith

/--
Case III-B residue bound.
-/
theorem lemma_1I_case_IIIB_residue_bound
  (n : ℕ)
  (hn : 15 ≤ n) :
  57 * (3 : ℤ)^(n - 2) < lemma_1I_case_IIIB_D n := by

  unfold lemma_1I_case_IIIB_D

  have h_core : ∀ t : ℕ, 105225318 * 3^t < 134217728 * 4^t := by
    intro t
    induction t with
    | zero =>
        norm_num
    | succ t ih =>
        calc
          105225318 * 3^(t + 1)
              = 3 * (105225318 * 3^t) := by ring
          _ < 3 * (134217728 * 4^t) := by
              exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
          _ ≤ 4 * (134217728 * 4^t) := by
              exact Nat.mul_le_mul_right (134217728 * 4^t) (by norm_num : 3 ≤ 4)
          _ = 134217728 * 4^(t + 1) := by ring

  let t := n - 15

  have hn_eq : n = t + 15 := by
    dsimp [t]
    omega

  rw [hn_eq]

  have h_left_nat :
      66 * 3^(t + 15 - 2) < 2 * 4^(t + 15 - 2) := by
    have h_left :
        66 * 3^(t + 15 - 2) = 105225318 * 3^t := by
      have h_exp : t + 15 - 2 = t + 13 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    have h_right :
        2 * 4^(t + 15 - 2) = 134217728 * 4^t := by
      have h_exp : t + 15 - 2 = t + 13 := by omega
      rw [h_exp, pow_add]
      norm_num
      ring

    rw [h_left, h_right]
    exact h_core t

  have h_left_int :
      66 * (3 : ℤ)^(t + 15 - 2) <
        2 * (4 : ℤ)^(t + 15 - 2) := by
    exact_mod_cast h_left_nat

  have h_pow2_to_four :
      (2 : ℤ)^(2 * (t + 15) - 3) =
        2 * (4 : ℤ)^(t + 15 - 2) := by
    have h_exp : 2 * (t + 15) - 3 = 2 * (t + 15 - 2) + 1 := by omega
    rw [h_exp, pow_add, pow_mul]
    norm_num
    ring

  have h_pow3 :
      (3 : ℤ)^(t + 15) =
        9 * (3 : ℤ)^(t + 15 - 2) := by
    have h_exp : t + 15 = (t + 15 - 2) + 2 := by omega
    rw [h_exp, pow_add]
    norm_num
    ring

  rw [h_pow2_to_four, h_pow3]
  nlinarith

/--
Lemma 1I, Case III-B closure.
-/
theorem lemma_1I_case_IIIB_no_integer_ratio
  (n Z : ℕ)
  (hn : 5 ≤ n)
  (hZ : lemma_1I_case_IIIB_ratio_integral_candidate n Z) :
  False := by

  by_cases hn_ge_fifteen : 15 ≤ n

  · exact
      lemma_1I_case_IIIB_no_integer_ratio_of_residue_bound
        n Z
        (by omega)
        (lemma_1I_case_IIIB_residue_bound n hn_ge_fifteen)
        hZ

  · have hn_le_fourteen : n ≤ 14 := by omega
    interval_cases n <;>
      norm_num
        [lemma_1I_case_IIIB_ratio_integral_candidate,
         lemma_1I_case_IIIB_N,
         lemma_1I_case_IIIB_D,
         lemma_1I_case_II_N] at hZ <;>
      omega
#check lemma_1I_no_lift_core
#check lemma_1I_case_I_terminal_unperturbed
#check lemma_1I_case_II_penultimate_negative
#check lemma_1I_case_IIIA_final_negative_only
#check lemma_1I_case_IIIB_both_terminal_negative

#check lemma_1I_case_I_N
#check lemma_1I_case_I_D
#check lemma_1I_case_II_N
#check lemma_1I_case_II_D
#check lemma_1I_case_IIIA_N
#check lemma_1I_case_IIIA_D
#check lemma_1I_case_IIIB_N
#check lemma_1I_case_IIIB_D

#check lemma_1I_case_I_ratio_integral_candidate
#check lemma_1I_case_II_ratio_integral_candidate
#check lemma_1I_case_IIIA_ratio_integral_candidate
#check lemma_1I_case_IIIB_ratio_integral_candidate

#check lemma_1I_case_I_no_integer_ratio_of_denominator_bound
#check lemma_1I_case_I_five_mul_three_pow_lt_two_pow
#check lemma_1I_case_I_denominator_bound
#check lemma_1I_case_I_no_integer_ratio

#check lemma_1I_case_II_fifteen_mul_three_pow_lt_four_pow
#check lemma_1I_case_II_no_integer_ratio

#check lemma_1I_case_IIIA_no_integer_ratio_of_residue_bound
#check lemma_1I_case_IIIA_residue_bound
#check lemma_1I_case_IIIA_no_integer_ratio

#check lemma_1I_case_IIIB_no_integer_ratio_of_residue_bound
#check lemma_1I_case_IIIB_residue_bound
#check lemma_1I_case_IIIB_no_integer_ratio

#print axioms lemma_1I_case_I_no_integer_ratio
#print axioms lemma_1I_case_II_no_integer_ratio
#print axioms lemma_1I_case_IIIA_no_integer_ratio
#print axioms lemma_1I_case_IIIB_no_integer_ratio
-- ===============================================================
-- COROLLARY 1I-1: CLOSURE OF THE PURE NEGATIVE BRANCH
-- ===============================================================

/--
Corollary 1I-1 pure negative branch signature.

The pure negative no-lift branch is exhausted by the four terminal cases of
Lemma 1I.
-/
def corollary_1I_1_pure_negative_branch (n x : ℕ) : Prop :=
  lemma_1I_case_I_terminal_unperturbed n x ∨
    lemma_1I_case_II_penultimate_negative n x ∨
      lemma_1I_case_IIIA_final_negative_only n x ∨
        lemma_1I_case_IIIB_both_terminal_negative n x

end Section21_Lemma1I_No_Lift_Floor

-- ===============================================================
-- SECTION 22: LEMMA 1J (MECHANISM-2 RATIO CEILING)
-- ===============================================================

section Section22_Lemma1J_Ratio_Ceiling

/--
Lemma 1J, bridge index.

For the genuine Mechanism-2 lifted branch, the bridge index is

`q = n - floor - 1`.

Here `floor` is the manuscript's internal valuation floor. We avoid the name
`p` in Lean to keep it distinct from other uses.
-/
def lemma_1J_bridge_index (n floor : ℕ) : ℕ :=
  n - floor - 1

/--
Lemma 1J, signed prefix deviation.

This is the manuscript quantity

`e_k = S_k - 2k`.

It is already represented in the codebase by `S_prime`.
-/
noncomputable def lemma_1J_e (k x : ℕ) : ℤ :=
  S_prime k x

/--
Lemma 1J, numerator-deviation term.

This is the manuscript term

`T_k = 3^(n-k) * (2^(S_{k-1}) - 2^(2k-2))`.

The index range is `1 ≤ k ≤ n`.
-/
noncomputable def lemma_1J_T (n x k : ℕ) : ℤ :=
  (3 : ℤ)^(n - k) *
    ((2 : ℤ)^(S (k - 1) x) - (2 : ℤ)^(2 * k - 2))

/--
Lemma 1J, first negative geometric block.

This is

`GP_1 = sum_{k=1}^{q} T_k`.
-/
noncomputable def lemma_1J_GP1 (n x floor : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 (lemma_1J_bridge_index n floor + 1),
    lemma_1J_T n x k

/--
Lemma 1J, positive lifted-tail block.

This is

`GP_2 = sum_{k=q+2}^{n} T_k`.
-/
noncomputable def lemma_1J_GP2 (n x floor : ℕ) : ℤ :=
  ∑ k ∈ Ico (lemma_1J_bridge_index n floor + 2) (n + 1),
    lemma_1J_T n x k

/--
Lemma 1J, denominator scale.

This is the manuscript quantity

`L = 2^(S_n)`.
-/
noncomputable def lemma_1J_L (n x : ℕ) : ℤ :=
  (2 : ℤ)^(S n x)

/--
Lemma 1J, maximal-ratio minimal-lift representative.

This is the exact exponent profile studied in Lemma 1J.

In Lean zero-indexed notation, `val ((T^[i]) x)` is the manuscript exponent
`a_{i+1}`.
-/
def lemma_1J_minimal_lift_representative
  (n x floor : ℕ) : Prop :=
  let q := lemma_1J_bridge_index n floor
  2 ≤ floor ∧
    2 ≤ q ∧
      q + 1 ≤ n - 2 ∧
        val ((T^[0]) x) = 1 ∧
          (∀ i ∈ Ico 1 (q - 1),
            val ((T^[i]) x) = 2) ∧
          val ((T^[q - 1]) x) = 1 ∧
          val ((T^[q]) x) = 6 ∧
          (∀ i ∈ Ico (q + 1) (n - 2),
            val ((T^[i]) x) =
              2 + 4 * 3^(i - q - 1)) ∧
          val ((T^[n - 2]) x) = 1 ∧
          val ((T^[n - 1]) x) = 1

#check lemma_1J_bridge_index
#check lemma_1J_e
#check lemma_1J_T
#check lemma_1J_GP1
#check lemma_1J_GP2
#check lemma_1J_L
#check lemma_1J_minimal_lift_representative
/--
Lemma 1J, first deviation.

From `a_1 = 1`, the first signed deviation is `e_1 = -1`.
-/
lemma lemma_1J_e_one
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_e 1 x = -1 := by

  rcases h_rep with
    ⟨_, _, _, h_first, _, _, _, _, _, _⟩

  have h_first0 :
      val x = 1 := by
    simpa using h_first

  unfold lemma_1J_e
  unfold S_prime
  unfold delta
  simp [h_first0]

/--
Lemma 1J, coasting deviations.

During the no-lift coasting segment, the signed deviation stays equal to `-1`.
-/
lemma lemma_1J_e_coasting
  (n x floor j : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (hj : j ∈ Ico 1 (lemma_1J_bridge_index n floor)) :
  lemma_1J_e j x = -1 := by

  rcases h_rep with
    ⟨_, _, _, h_first, h_coast, _, _, _, _, _⟩

  revert hj

  induction j with
  | zero =>
      intro hj
      rw [mem_Ico] at hj
      omega

  | succ j ih =>
      intro hj

      by_cases hj_zero : j = 0

      · subst j

        have h_first0 :
            val x = 1 := by
          simpa using h_first

        unfold lemma_1J_e
        unfold S_prime
        unfold delta
        simp [h_first0]

      · have hj_prev :
            j ∈ Ico 1 (lemma_1J_bridge_index n floor) := by
          rw [mem_Ico] at hj ⊢
          omega

        have h_prev :
            lemma_1J_e j x = -1 :=
          ih hj_prev

        unfold lemma_1J_e at h_prev ⊢

        rw [S_prime_succ x j]
        rw [h_prev]

        have h_val :
            val ((T^[j]) x) = 2 := by
          apply h_coast
          rw [mem_Ico] at hj ⊢
          omega

        unfold delta
        rw [h_val]
        norm_num

/--
Lemma 1J, bridge deviation.

At the bridge index `q`, the signed deviation drops to `-2`.
-/
lemma lemma_1J_e_bridge
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_e (lemma_1J_bridge_index n floor) x = -2 := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, hq_ge, _, _, _, h_bridge, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  have h_prev :
      lemma_1J_e (q - 1) x = -1 := by
    exact
      lemma_1J_e_coasting
        n x floor (q - 1)
        h_rep_copy
        (by
          rw [mem_Ico]
          dsimp [q]
          omega)

  have hq_succ :
      q = (q - 1) + 1 := by
    omega

  unfold lemma_1J_e at h_prev ⊢

  change S_prime q x = -2

  rw [hq_succ]
  rw [S_prime_succ x (q - 1)]
  rw [h_prev]

  have h_bridge_q :
      val ((T^[q - 1]) x) = 1 := by
    dsimp [q]
    exact h_bridge

  unfold delta
  rw [h_bridge_q]
  norm_num

#check lemma_1J_e_one
#check lemma_1J_e_coasting
#check lemma_1J_e_bridge

/--
Lemma 1J, first lifted-tail deviation.

At `j = q + 1`, the bridge exponent `a_q = 1` is followed by the first
minimal lifted-tail exponent `a_{q+1} = 6`, so the deviation becomes `2`.
-/
lemma lemma_1J_e_lift_start
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_e (lemma_1J_bridge_index n floor + 1) x = 2 := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, _, _, _, _, _, h_lift_start, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  have h_bridge :
      lemma_1J_e q x = -2 := by
    dsimp [q]
    exact lemma_1J_e_bridge n x floor h_rep_copy

  unfold lemma_1J_e at h_bridge ⊢

  rw [S_prime_succ x q]
  rw [h_bridge]

  have h_val :
      val ((T^[q]) x) = 6 := by
    dsimp [q]
    exact h_lift_start

  unfold delta
  rw [h_val]
  norm_num

/--
Lemma 1J, lifted-tail deviations.

For every lifted-tail prefix through `n - 2`, the signed deviation is

`e_j = 2 * 3^(j - q - 1)`,

which is exactly the minimal `C = 1` tail.
-/
lemma lemma_1J_e_lift_tail
  (n x floor j : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (hj_low :
    lemma_1J_bridge_index n floor + 1 ≤ j)
  (hj_high : j ≤ n - 2) :
  lemma_1J_e j x =
    2 * (3 : ℤ)^(j - lemma_1J_bridge_index n floor - 1) := by

  let q := lemma_1J_bridge_index n floor

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, _, _, _, _, _, _, h_tail, _, _⟩

  change
    lemma_1J_e j x =
      2 * (3 : ℤ)^(j - q - 1)

  have hj_low_q : q + 1 ≤ j := by
    dsimp [q]
    exact hj_low

  rcases Nat.exists_eq_add_of_le hj_low_q with ⟨t, ht⟩
  subst j

  have h_ind :
      ∀ t,
        q + 1 + t ≤ n - 2 →
          lemma_1J_e (q + 1 + t) x =
            2 * (3 : ℤ)^(q + 1 + t - q - 1) := by
    intro t ht

    induction t with
    | zero =>
        have h_start :
            lemma_1J_e (q + 1) x = 2 := by
          dsimp [q]
          exact lemma_1J_e_lift_start n x floor h_rep_copy

        have h_exp :
            q + 1 + 0 - q - 1 = 0 := by
          omega

        simpa [h_exp] using h_start

    | succ t ih =>
        have ht_prev :
            q + 1 + t ≤ n - 2 := by
          omega

        have h_prev :
            lemma_1J_e (q + 1 + t) x =
              2 * (3 : ℤ)^(q + 1 + t - q - 1) :=
          ih ht_prev

        unfold lemma_1J_e at h_prev ⊢

        have h_succ_index :
            q + 1 + (t + 1) = (q + 1 + t) + 1 := by
          omega

        rw [h_succ_index]
        rw [S_prime_succ x (q + 1 + t)]
        rw [h_prev]

        have h_val :
            val ((T^[q + 1 + t]) x) =
              2 + 4 * 3^(q + 1 + t - q - 1) := by
          apply h_tail
          rw [mem_Ico]
          omega

        unfold delta
        rw [h_val]

        have h_exp_succ :
            q + 1 + t + 1 - q - 1 =
              (q + 1 + t - q - 1) + 1 := by
          omega

        rw [h_exp_succ, pow_succ]
        push_cast
        ring

  exact h_ind t (by omega)

#check lemma_1J_e_lift_start
#check lemma_1J_e_lift_tail

/--
Lemma 1J, penultimate deviation.

For the extremal terminal choice `a_{n-1} = 1`, the final numerator-visible
deviation is

`e_{n-1} = 2 * 3^(floor - 2) - 1`.
-/
lemma lemma_1J_e_penultimate
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_e (n - 1) x =
    2 * (3 : ℤ)^(floor - 2) - 1 := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨h_floor, hq_ge, h_tail_end, _, _, _, _, _, h_pen, _⟩

  let q := lemma_1J_bridge_index n floor

  have hq_ge_unfold :
      2 ≤ n - floor - 1 := by
    simpa [q, lemma_1J_bridge_index] using hq_ge

  have h_floor_succ_le :
      floor + 1 ≤ n := by
    omega

  have h_sub :
      n - floor - 1 = n - (floor + 1) := by
    omega

  have hq_add :
      q + floor + 1 = n := by
    calc
      q + floor + 1
          =
        (n - floor - 1) + floor + 1 := by
          dsimp [q, lemma_1J_bridge_index]
      _ =
        (n - (floor + 1)) + (floor + 1) := by
          rw [h_sub]
          omega
      _ =
        n := by
          exact Nat.sub_add_cancel h_floor_succ_le

  have h_n2_tail :
      lemma_1J_e (n - 2) x =
        2 * (3 : ℤ)^((n - 2) - q - 1) := by
    have h :=
      lemma_1J_e_lift_tail
        n x floor (n - 2)
        h_rep_copy
        h_tail_end
        (by omega)
    simpa [q] using h

  have h_exp :
      (n - 2) - q - 1 = floor - 2 := by
    omega

  rw [h_exp] at h_n2_tail

  unfold lemma_1J_e at h_n2_tail ⊢

  have h_step :
      n - 1 = (n - 2) + 1 := by
    omega

  rw [h_step]
  rw [S_prime_succ x (n - 2)]
  rw [h_n2_tail]

  unfold delta
  rw [h_pen]
  ring

/--
Lemma 1J, total exponent sum.

For the extremal representative,

`S_n = 2*n - 2 + 2*3^(floor - 2)`.
-/
lemma lemma_1J_total_exponent
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  S n x = 2 * n - 2 + 2 * 3^(floor - 2) := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, hq_ge, _, _, _, _, _, _, _, h_fin⟩

  have hn_pos : 1 ≤ n := by
    omega

  have h_e_pen :
      lemma_1J_e (n - 1) x =
        2 * (3 : ℤ)^(floor - 2) - 1 :=
    lemma_1J_e_penultimate n x floor h_rep_copy

  unfold lemma_1J_e at h_e_pen

  have h_step :
      n = (n - 1) + 1 := by
    omega

  have h_Sn :
      (S n x : ℤ) =
        (S (n - 1) x : ℤ) + val ((T^[n - 1]) x) := by
    rw [h_step]
    simp [S]

  have h_rel :
      (S (n - 1) x : ℤ) =
        2 * ((n - 1 : ℕ) : ℤ) + S_prime (n - 1) x :=
    s_relationship (n - 1) x

  have h_nminus_cast :
      ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by
    rw [Nat.cast_sub hn_pos]
    omega

  have h_int :
      (S n x : ℤ) =
        2 * (n : ℤ) - 2 + 2 * (3 : ℤ)^(floor - 2) := by
    rw [h_Sn]
    rw [h_rel]
    rw [h_e_pen]
    rw [h_fin]
    rw [h_nminus_cast]
    omega

  have h_rhs_cast :
      ((2 * n - 2 + 2 * 3^(floor - 2) : ℕ) : ℤ) =
        2 * (n : ℤ) - 2 + 2 * (3 : ℤ)^(floor - 2) := by
    have h_two_le : 2 ≤ 2 * n := by
      omega
    rw [Nat.cast_add]
    rw [Nat.cast_sub h_two_le]
    push_cast
    omega

  exact (Int.ofNat.inj
    (h_int.trans h_rhs_cast.symm))

#check lemma_1J_e_penultimate
#check lemma_1J_total_exponent

/--
Lemma 1J, first numerator-deviation term.

The term `T_1` is zero.
-/
lemma lemma_1J_T_one_zero
  (n x : ℕ) :
  lemma_1J_T n x 1 = 0 := by

  unfold lemma_1J_T
  simp [S]

/--
Lemma 1J, coasting term evaluation.

For `2 ≤ k ≤ q`, the coasting deviation is `e_{k-1} = -1`, hence

`T_k = -3^(n-k) * 2^(2k-3)`.
-/
lemma lemma_1J_T_coasting_eq
  (n x floor k : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (hk_low : 2 ≤ k)
  (hk_high : k ≤ lemma_1J_bridge_index n floor) :
  lemma_1J_T n x k =
    - (3 : ℤ)^(n - k) * (2 : ℤ)^(2 * k - 3) := by

  have h_prev_mem :
      k - 1 ∈ Ico 1 (lemma_1J_bridge_index n floor) := by
    rw [mem_Ico]
    omega

  have h_e :
      lemma_1J_e (k - 1) x = -1 :=
    lemma_1J_e_coasting n x floor (k - 1) h_rep h_prev_mem

  unfold lemma_1J_e at h_e

  have h_rel :
      (S (k - 1) x : ℤ) =
        2 * ((k - 1 : ℕ) : ℤ) + S_prime (k - 1) x :=
    s_relationship (k - 1) x

  rw [h_e] at h_rel

  have h_k_cast :
      ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    ring

  have hS_int :
      (S (k - 1) x : ℤ) = 2 * (k : ℤ) - 3 := by
    rw [h_k_cast] at h_rel
    omega

  have h_rhs_cast :
      ((2 * k - 3 : ℕ) : ℤ) = 2 * (k : ℤ) - 3 := by
    have h_le : 3 ≤ 2 * k := by
      omega
    rw [Nat.cast_sub h_le]
    push_cast
    ring

  have hS_nat :
      S (k - 1) x = 2 * k - 3 :=
    Int.ofNat.inj (hS_int.trans h_rhs_cast.symm)

  unfold lemma_1J_T
  rw [hS_nat]

  have h_exp :
      2 * k - 2 = (2 * k - 3) + 1 := by
    omega

  rw [h_exp, pow_succ]
  ring

/--
Lemma 1J, first geometric block is negative.

This proves the manuscript conclusion `GP_1 < 0`.
-/
lemma lemma_1J_GP1_neg
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_GP1 n x floor < 0 := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, hq_ge, _, _, _, _, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  have h_two_mem :
      2 ∈ Ico 1 (q + 1) := by
    rw [mem_Ico]
    dsimp [q]
    omega

  let f : ℕ → ℤ := fun k => lemma_1J_T n x k

  unfold lemma_1J_GP1
  change (∑ k ∈ Ico 1 (q + 1), f k) < 0

  rw [← sum_erase_add _ _ h_two_mem]

  have h_rest_nonpos :
      ∑ k ∈ (Ico 1 (q + 1)).erase 2, f k ≤ 0 := by
    apply sum_nonpos
    intro k hk

    have hk_parts := mem_erase.mp hk
    have hk_mem : k ∈ Ico 1 (q + 1) := hk_parts.2

    by_cases hk_one : k = 1

    · subst k
      dsimp [f]
      rw [lemma_1J_T_one_zero]

    · have hk_low : 2 ≤ k := by
        rw [mem_Ico] at hk_mem
        omega

      have hk_high : k ≤ lemma_1J_bridge_index n floor := by
        rw [mem_Ico] at hk_mem
        dsimp [q] at hk_mem
        omega

      dsimp [f]
      rw [lemma_1J_T_coasting_eq n x floor k h_rep_copy hk_low hk_high]

      have h_nonneg :
          0 ≤ (3 : ℤ)^(n - k) * (2 : ℤ)^(2 * k - 3) := by
        positivity

      linarith

  have h_two_neg :
      f 2 < 0 := by
    dsimp [f]
    rw [lemma_1J_T_coasting_eq n x floor 2 h_rep_copy (by norm_num) hq_ge]

    have h_pos :
        0 < (3 : ℤ)^(n - 2) * (2 : ℤ)^(2 * 2 - 3) := by
      positivity

    linarith

  linarith

#check lemma_1J_T_one_zero
#check lemma_1J_T_coasting_eq
#check lemma_1J_GP1_neg

/--
Lemma 1J, bridge term evaluation.

At the bridge output, `e_q = -2`, so

`T_{q+1} = -3^(n-q) * 2^(2q-2)`.
-/
lemma lemma_1J_T_bridge_eq
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_T n x (lemma_1J_bridge_index n floor + 1) =
    - (3 : ℤ)^(n - lemma_1J_bridge_index n floor) *
      (2 : ℤ)^(2 * lemma_1J_bridge_index n floor - 2) := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨_, hq_ge, h_tail_end, _, _, _, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  change
    lemma_1J_T n x (q + 1) =
      - (3 : ℤ)^(n - q) * (2 : ℤ)^(2 * q - 2)

  have h_e_bridge :
      S_prime q x = -2 := by
    have h :=
      lemma_1J_e_bridge n x floor h_rep_copy
    unfold lemma_1J_e at h
    simpa [q] using h

  have h_rel :
      (S q x : ℤ) =
        2 * (q : ℤ) + S_prime q x :=
    s_relationship q x

  rw [h_e_bridge] at h_rel

  have hS_int :
      (S q x : ℤ) = 2 * (q : ℤ) - 2 := by
    omega

  have h_rhs_cast :
      ((2 * q - 2 : ℕ) : ℤ) =
        2 * (q : ℤ) - 2 := by
    have h_le : 2 ≤ 2 * q := by
      omega
    rw [Nat.cast_sub h_le]
    push_cast
    ring

  have hS_nat :
      S q x = 2 * q - 2 :=
    Int.ofNat.inj (hS_int.trans h_rhs_cast.symm)

  unfold lemma_1J_T

  have h_pred :
      q + 1 - 1 = q := by
    omega

  rw [h_pred]
  rw [hS_nat]

  have h_two_exp :
      2 * (q + 1) - 2 = (2 * q - 2) + 2 := by
    omega

  have h_three_exp :
      n - q = (n - (q + 1)) + 1 := by
    omega

  rw [h_two_exp]
  rw [pow_add]
  norm_num
  rw [h_three_exp]
  rw [pow_succ]
  ring

/--
Lemma 1J, bridge term negativity.

This proves the manuscript conclusion `T_{q+1} < 0`.
-/
lemma lemma_1J_T_bridge_neg
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_T n x (lemma_1J_bridge_index n floor + 1) < 0 := by

  rw [lemma_1J_T_bridge_eq n x floor h_rep]

  have h_pos :
      0 <
        (3 : ℤ)^(n - lemma_1J_bridge_index n floor) *
          (2 : ℤ)^(2 * lemma_1J_bridge_index n floor - 2) := by
    positivity

  linarith

#check lemma_1J_T_bridge_eq
#check lemma_1J_T_bridge_neg
/--
Lemma 1J, numerator-visible upper bound for one deviation term.

For every `k`, the deviation term is strictly smaller than its corresponding
numerator-visible term:

`T_k < 3^(n-k) * 2^(S_{k-1})`.
-/
lemma lemma_1J_T_lt_visible_term
  (n x k : ℕ) :
  lemma_1J_T n x k <
    (3 : ℤ)^(n - k) * (2 : ℤ)^(S (k - 1) x) := by

  unfold lemma_1J_T

  have h_three_pos :
      0 < (3 : ℤ)^(n - k) := by
    positivity

  have h_sub_lt :
      (2 : ℤ)^(S (k - 1) x) - (2 : ℤ)^(2 * k - 2)
        <
      (2 : ℤ)^(S (k - 1) x) := by
    have h_pow_pos :
        0 < (2 : ℤ)^(2 * k - 2) := by
      positivity
    linarith

  exact mul_lt_mul_of_pos_left h_sub_lt h_three_pos

#check lemma_1J_T_lt_visible_term
/--
Lemma 1J, final visible term bound.

Since `a_n = 1`, the final numerator-visible term satisfies

`2 * 2^(S_{n-1}) = L`.
-/
lemma lemma_1J_final_visible_twice_eq_L
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  2 * (2 : ℤ)^(S (n - 1) x) = lemma_1J_L n x := by

  rcases h_rep with
    ⟨_, _, _, _, _, _, _, _, _, h_fin⟩

  have hn_pos : 1 ≤ n := by
    omega

  have h_step :
      n = (n - 1) + 1 := by
    omega

  have h_Sn :
      S n x = S (n - 1) x + val ((T^[n - 1]) x) := by
    rw [h_step]
    simp [S]

  rw [h_fin] at h_Sn

  unfold lemma_1J_L
  rw [h_Sn]
  rw [pow_add]
  norm_num
  ring

/--
Lemma 1J, penultimate visible term bound.

Since `a_{n-1}=a_n=1`, the penultimate numerator-visible term satisfies

`4 * (3 * 2^(S_{n-2})) = 3 * L`.
-/
lemma lemma_1J_penultimate_visible_four_eq_three_L
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  4 * ((3 : ℤ) * (2 : ℤ)^(S (n - 2) x)) =
    3 * lemma_1J_L n x := by

  rcases h_rep with
    ⟨_, _, _, _, _, _, _, _, h_pen, h_fin⟩

  have hn_ge_two : 2 ≤ n := by
    omega

  have h_step_pen :
      n - 1 = (n - 2) + 1 := by
    omega

  have h_step_fin :
      n = (n - 1) + 1 := by
    omega

  have h_S_pen :
      S (n - 1) x =
        S (n - 2) x + val ((T^[n - 2]) x) := by
    rw [h_step_pen]
    simp [S]

  have h_S_fin :
      S n x =
        S (n - 1) x + val ((T^[n - 1]) x) := by
    rw [h_step_fin]
    simp [S]

  rw [h_pen] at h_S_pen
  rw [h_fin] at h_S_fin
  rw [h_S_pen] at h_S_fin

  unfold lemma_1J_L
  rw [h_S_fin]
  rw [pow_add]
  norm_num
  ring

#check lemma_1J_final_visible_twice_eq_L
#check lemma_1J_penultimate_visible_four_eq_three_L

/--
Lemma 1J, first earlier lifted visible bound.

The manuscript bound

`9 * 2^(S_{n-3}) ≤ 9L/256`

is encoded without division as

`256 * (9 * 2^(S_{n-3})) ≤ 9L`.
-/
lemma lemma_1J_nminus_two_visible_bound
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  256 * ((9 : ℤ) * (2 : ℤ)^(S (n - 3) x)) ≤
    9 * lemma_1J_L n x := by

  rcases h_rep with
    ⟨_, hq_ge, h_tail_end, _, _, _, h_lift_start, h_tail, h_pen, h_fin⟩

  let q := lemma_1J_bridge_index n floor

  have h_tail_end_q :
      q + 1 ≤ n - 2 := by
    dsimp [q]
    exact h_tail_end

  have hn_ge_three : 3 ≤ n := by
    omega

  have h_a_nminus2_ge_six :
      6 ≤ val ((T^[n - 3]) x) := by
    by_cases h_edge : n - 3 = q

    · have h_val :
          val ((T^[n - 3]) x) = 6 := by
        rw [h_edge]
        dsimp [q]
        exact h_lift_start
      rw [h_val]

    · have h_nminus3_tail_mem :
          n - 3 ∈ Ico (q + 1) (n - 2) := by
        rw [mem_Ico]
        constructor
        · omega
        · omega

      have h_val :
          val ((T^[n - 3]) x) =
            2 + 4 * 3^(n - 3 - q - 1) := by
        have h_mem_original :
            n - 3 ∈
              Ico (lemma_1J_bridge_index n floor + 1) (n - 2) := by
          simpa [q] using h_nminus3_tail_mem
        exact h_tail (n - 3) h_mem_original

      rw [h_val]

      have h_pow_pos :
          1 ≤ 3^(n - 3 - q - 1) := by
        exact Nat.one_le_pow _ _ (by norm_num)

      nlinarith

  have h_step_1 :
      n - 2 = (n - 3) + 1 := by
    omega

  have h_step_2 :
      n - 1 = (n - 2) + 1 := by
    omega

  have h_step_3 :
      n = (n - 1) + 1 := by
    omega

  have hS_n2 :
      S (n - 2) x =
        S (n - 3) x + val ((T^[n - 3]) x) := by
    rw [h_step_1]
    simp [S]

  have hS_n1 :
      S (n - 1) x =
        S (n - 2) x + val ((T^[n - 2]) x) := by
    rw [h_step_2]
    simp [S]

  have hS_n :
      S n x =
        S (n - 1) x + val ((T^[n - 1]) x) := by
    rw [h_step_3]
    simp [S]

  rw [h_pen] at hS_n1
  rw [h_fin] at hS_n
  rw [hS_n2] at hS_n1
  rw [hS_n1] at hS_n

  have h_gap :
      S (n - 3) x + 8 ≤ S n x := by
    omega

  have h_pow_le :
      (2 : ℤ)^8 * (2 : ℤ)^(S (n - 3) x) ≤
        (2 : ℤ)^(S n x) := by
    have h_raw :
        (2 : ℤ)^(S (n - 3) x + 8) ≤ (2 : ℤ)^(S n x) := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_gap

    have h_rewrite :
        (2 : ℤ)^(S (n - 3) x + 8) =
          (2 : ℤ)^8 * (2 : ℤ)^(S (n - 3) x) := by
      rw [pow_add]
      ring

    rw [h_rewrite] at h_raw
    exact h_raw

  unfold lemma_1J_L
  norm_num at h_pow_le ⊢
  nlinarith

#check lemma_1J_nminus_two_visible_bound

/--
Lemma 1J, numerator-visible term.

This is the corresponding numerator-visible term bounding `T_k`:

`3^(n-k) * 2^(S_{k-1})`.
-/
noncomputable def lemma_1J_visible_term (n x k : ℕ) : ℤ :=
  (3 : ℤ)^(n - k) * (2 : ℤ)^(S (k - 1) x)

/--
Lemma 1J, lifted-tail exponents are at least six.

Inside the lifted tail, every exponent used in the backward ratio estimate
satisfies `a_i ≥ 6`.
-/
lemma lemma_1J_lift_tail_exponent_ge_six
  (n x floor i : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (hi :
    i ∈ Ico (lemma_1J_bridge_index n floor + 1) (n - 2)) :
  6 ≤ val ((T^[i]) x) := by

  rcases h_rep with
    ⟨_, _, _, _, _, _, _, h_tail, _, _⟩

  have h_val :
      val ((T^[i]) x) =
        2 + 4 * 3^(i - lemma_1J_bridge_index n floor - 1) :=
    h_tail i hi

  rw [h_val]

  have h_pow_pos :
      1 ≤ 3^(i - lemma_1J_bridge_index n floor - 1) := by
    exact Nat.one_le_pow _ _ (by norm_num)

  nlinarith

/--
Lemma 1J, backward visible-term ratio.

Moving one step backward through the lifted tail gives the manuscript ratio

`visible(k-1) / visible(k) ≤ 3/64`.

This is encoded without division as

`64 * visible(k-1) ≤ 3 * visible(k)`.
-/
lemma lemma_1J_visible_backward_ratio
  (n x floor k : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (hk_low : lemma_1J_bridge_index n floor + 3 ≤ k)
  (hk_high : k ≤ n - 2) :
  64 * lemma_1J_visible_term n x (k - 1) ≤
    3 * lemma_1J_visible_term n x k := by

  let q := lemma_1J_bridge_index n floor

  have h_i_mem :
      k - 2 ∈ Ico (lemma_1J_bridge_index n floor + 1) (n - 2) := by
    rw [mem_Ico]
    omega

  have h_exp_ge_six :
      6 ≤ val ((T^[k - 2]) x) :=
    lemma_1J_lift_tail_exponent_ge_six
      n x floor (k - 2) h_rep h_i_mem

  have h_step :
      k - 1 = (k - 2) + 1 := by
    omega

  have hS_step :
      S (k - 1) x =
        S (k - 2) x + val ((T^[k - 2]) x) := by
    rw [h_step]
    simp [S]

  have h_pred :
      k - 1 - 1 = k - 2 := by
    omega

  have h_three_exp :
      n - (k - 1) = (n - k) + 1 := by
    omega

  have h_pow64_le :
      (64 : ℤ) ≤ (2 : ℤ)^(val ((T^[k - 2]) x)) := by
    have h_raw :
        (2 : ℤ)^6 ≤ (2 : ℤ)^(val ((T^[k - 2]) x)) := by
      exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_exp_ge_six

    norm_num at h_raw
    exact h_raw

  unfold lemma_1J_visible_term

  rw [h_pred]
  rw [h_three_exp]
  rw [pow_succ]
  rw [hS_step]
  rw [pow_add]

  have h_factor_nonneg :
      0 ≤
        (3 : ℤ) *
          ((3 : ℤ)^(n - k) * (2 : ℤ)^(S (k - 2) x)) := by
    positivity

  have h_scaled :
      (3 : ℤ) *
          ((3 : ℤ)^(n - k) * (2 : ℤ)^(S (k - 2) x)) *
          64
        ≤
      (3 : ℤ) *
          ((3 : ℤ)^(n - k) * (2 : ℤ)^(S (k - 2) x)) *
          (2 : ℤ)^(val ((T^[k - 2]) x)) := by
    exact mul_le_mul_of_nonneg_left h_pow64_le h_factor_nonneg

  ring_nf at h_scaled ⊢
  exact h_scaled

#check lemma_1J_visible_term
#check lemma_1J_lift_tail_exponent_ge_six
#check lemma_1J_visible_backward_ratio
/--
Lemma 1J, finite backward geometric bound.

For any starting index `a` inside the earlier lifted visible tail, the finite
tail sum satisfies the manuscript geometric estimate

`61 * sum + 3 * first ≤ 64 * last`.

Dropping the nonnegative `3 * first` gives the usual
`sum ≤ (64/61) * last`.
-/
lemma lemma_1J_visible_tail_geometric_from
  (n x floor a : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor)
  (ha_low : lemma_1J_bridge_index n floor + 2 ≤ a)
  (ha_high : a ≤ n - 2) :
  61 *
      (∑ k ∈ Ico a (n - 1),
        lemma_1J_visible_term n x k) +
    3 * lemma_1J_visible_term n x a
      ≤
    64 * lemma_1J_visible_term n x (n - 2) := by

  let q := lemma_1J_bridge_index n floor

  have h_ind :
      ∀ d a,
        a + d = n - 2 →
        q + 2 ≤ a →
          61 *
              (∑ k ∈ Ico a (n - 1),
                lemma_1J_visible_term n x k) +
            3 * lemma_1J_visible_term n x a
              ≤
            64 * lemma_1J_visible_term n x (n - 2) := by
    intro d
    induction d with
    | zero =>
        intro a ha_eq ha_low_a

        have ha_eq_n2 :
            a = n - 2 := by
          omega

        subst a

        have h_singleton :
            Ico (n - 2) (n - 1) = ({n - 2} : Finset ℕ) := by
          ext k
          rw [mem_Ico, mem_singleton]
          constructor
          · intro hk
            omega
          · intro hk
            subst k
            omega

        rw [h_singleton]
        simp
        ring_nf
        exact le_rfl

    | succ d ih =>
        intro a ha_eq ha_low_a

        have ha_lt :
            a < n - 2 := by
          omega

        have h_ih :
            61 *
                (∑ k ∈ Ico (a + 1) (n - 1),
                  lemma_1J_visible_term n x k) +
              3 * lemma_1J_visible_term n x (a + 1)
                ≤
              64 * lemma_1J_visible_term n x (n - 2) :=
          ih (a + 1) (by omega) (by omega)

        have h_ratio :
            64 * lemma_1J_visible_term n x a
              ≤
            3 * lemma_1J_visible_term n x (a + 1) := by
          have h_raw :
              64 * lemma_1J_visible_term n x ((a + 1) - 1)
                ≤
              3 * lemma_1J_visible_term n x (a + 1) :=
            lemma_1J_visible_backward_ratio
              n x floor (a + 1) h_rep
              (by
                dsimp [q] at ha_low_a ⊢
                omega)
              (by omega)

          have h_pred :
              (a + 1) - 1 = a := by
            omega

          rwa [h_pred] at h_raw

        have ha_mem :
            a ∈ Ico a (n - 1) := by
          rw [mem_Ico]
          omega

        have h_erase :
            (Ico a (n - 1)).erase a = Ico (a + 1) (n - 1) := by
          ext k
          rw [mem_erase, mem_Ico, mem_Ico]
          constructor
          · intro hk
            exact ⟨by omega, hk.2.2⟩
          · intro hk
            exact ⟨by omega, by omega, hk.2⟩

        rw [← sum_erase_add _ _ ha_mem]
        rw [h_erase]

        nlinarith [h_ih, h_ratio]

  let d := n - 2 - a

  have hd :
      a + d = n - 2 := by
    dsimp [d]
    omega

  exact h_ind d a hd (by
    dsimp [q]
    exact ha_low)

/--
Lemma 1J, earlier lifted visible-tail bound.

The manuscript bound

`earlier lifted visible part ≤ 9L/244`

is encoded without division as

`244 * earlier_sum ≤ 9L`.
-/
lemma lemma_1J_earlier_visible_tail_bound
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  244 *
      (∑ k ∈ Ico (lemma_1J_bridge_index n floor + 2) (n - 1),
        lemma_1J_visible_term n x k)
    ≤
  9 * lemma_1J_L n x := by

  have h_rep_bounds := h_rep

  rcases h_rep_bounds with
    ⟨_, _, h_tail_end, _, _, _, _, _, _, _⟩

  have hn_ge_two : 2 ≤ n := by
    omega

  have h_visible_n2 :
      lemma_1J_visible_term n x (n - 2) =
        (9 : ℤ) * (2 : ℤ)^(S (n - 3) x) := by
    unfold lemma_1J_visible_term

    have h_pred :
        n - 2 - 1 = n - 3 := by
      omega

    have h_three :
        n - (n - 2) = 2 := by
      omega

    rw [h_pred, h_three]
    norm_num

  have h_base :
      256 * lemma_1J_visible_term n x (n - 2) ≤
        9 * lemma_1J_L n x := by
    have h :=
      lemma_1J_nminus_two_visible_bound n x floor h_rep
    rw [← h_visible_n2] at h
    exact h

  by_cases h_nonempty :
      lemma_1J_bridge_index n floor + 2 ≤ n - 2

  · have h_geom :
        61 *
            (∑ k ∈ Ico (lemma_1J_bridge_index n floor + 2) (n - 1),
              lemma_1J_visible_term n x k) +
          3 *
            lemma_1J_visible_term n x
              (lemma_1J_bridge_index n floor + 2)
            ≤
          64 * lemma_1J_visible_term n x (n - 2) :=
      lemma_1J_visible_tail_geometric_from
        n x floor
        (lemma_1J_bridge_index n floor + 2)
        h_rep
        (by omega)
        h_nonempty

    have h_extra_nonneg :
        0 ≤
          3 *
            lemma_1J_visible_term n x
              (lemma_1J_bridge_index n floor + 2) := by
      unfold lemma_1J_visible_term
      positivity

    have h_sum_bound :
        61 *
            (∑ k ∈ Ico (lemma_1J_bridge_index n floor + 2) (n - 1),
              lemma_1J_visible_term n x k)
          ≤
        64 * lemma_1J_visible_term n x (n - 2) := by
      linarith

    nlinarith [h_sum_bound, h_base]

  · have h_empty :
        Ico (lemma_1J_bridge_index n floor + 2) (n - 1) =
          (∅ : Finset ℕ) := by
      ext k
      rw [mem_Ico]
      simp
      intro h_low
      omega

    rw [h_empty]
    simp
    unfold lemma_1J_L
    positivity

#check lemma_1J_visible_tail_geometric_from
#check lemma_1J_earlier_visible_tail_bound
/--
Lemma 1J, GP2 is bounded by the corresponding visible terms.

This is the summed form of the manuscript inequality

`T_k < 3^(n-k) * 2^(S_{k-1})`

over the positive lifted-tail block.
-/
lemma lemma_1J_GP2_lt_visible_sum
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  lemma_1J_GP2 n x floor <
    ∑ k ∈ Ico (lemma_1J_bridge_index n floor + 2) (n + 1),
      lemma_1J_visible_term n x k := by

  rcases h_rep with
    ⟨_, _, h_tail_end, _, _, _, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  unfold lemma_1J_GP2
  change
    (∑ k ∈ Ico (q + 2) (n + 1), lemma_1J_T n x k) <
      ∑ k ∈ Ico (q + 2) (n + 1),
        lemma_1J_visible_term n x k

  apply sum_lt_sum

  · intro k hk
    simpa [lemma_1J_visible_term] using
      le_of_lt (lemma_1J_T_lt_visible_term n x k)

  · refine ⟨q + 2, ?_, ?_⟩

    · rw [mem_Ico]
      omega

    · simpa [lemma_1J_visible_term] using
        lemma_1J_T_lt_visible_term n x (q + 2)

/--
Lemma 1J, visible GP2 bound.

The manuscript bound

`GP_2 < 157/122 L`

is encoded without division as

`244 * GP_2 < 314 * L`.
-/
lemma lemma_1J_GP2_bound
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  244 * lemma_1J_GP2 n x floor <
    314 * lemma_1J_L n x := by

  have h_rep_bounds := h_rep

  rcases h_rep_bounds with
    ⟨_, _, h_tail_end, _, _, _, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  have hn_ge_three : 3 ≤ n := by
    omega

  have h_gp2_visible :
      lemma_1J_GP2 n x floor <
        ∑ k ∈ Ico (q + 2) (n + 1),
          lemma_1J_visible_term n x k := by
    dsimp [q]
    exact lemma_1J_GP2_lt_visible_sum n x floor h_rep

  have h_split :
      (∑ k ∈ Ico (q + 2) (n + 1),
        lemma_1J_visible_term n x k)
      =
      (∑ k ∈ Ico (q + 2) (n - 1),
        lemma_1J_visible_term n x k)
      + lemma_1J_visible_term n x (n - 1)
      + lemma_1J_visible_term n x n := by

    have h_nminus1_mem :
        n - 1 ∈ Ico (q + 2) (n + 1) := by
      rw [mem_Ico]
      omega

    have h_n_mem :
        n ∈ (Ico (q + 2) (n + 1)).erase (n - 1) := by
      rw [mem_erase, mem_Ico]
      constructor
      · omega
      · omega

    rw [← sum_erase_add _ _ h_nminus1_mem]
    rw [← sum_erase_add _ _ h_n_mem]

    have h_erase_twice :
        ((Ico (q + 2) (n + 1)).erase (n - 1)).erase n =
          Ico (q + 2) (n - 1) := by
      ext k
      rw [mem_erase, mem_erase, mem_Ico, mem_Ico]
      constructor
      · intro hk
        exact ⟨hk.2.2.1, by omega⟩
      · intro hk
        exact ⟨by omega, by omega, hk.1, by omega⟩

    rw [h_erase_twice]
    ring

  have h_final_visible :
      lemma_1J_visible_term n x n =
        (2 : ℤ)^(S (n - 1) x) := by
    unfold lemma_1J_visible_term

    have h_exp :
        n - n = 0 := by
      omega

    rw [h_exp]
    norm_num

  have h_pen_visible :
      lemma_1J_visible_term n x (n - 1) =
        (3 : ℤ) * (2 : ℤ)^(S (n - 2) x) := by
    unfold lemma_1J_visible_term

    have h_exp :
        n - (n - 1) = 1 := by
      omega

    have h_pred :
        n - 1 - 1 = n - 2 := by
      omega

    rw [h_exp, h_pred]
    norm_num

  have h_final_bound :
      488 * lemma_1J_visible_term n x n =
        244 * lemma_1J_L n x := by
    rw [h_final_visible]

    have h :=
      lemma_1J_final_visible_twice_eq_L n x floor h_rep

    calc
      488 * (2 : ℤ)^(S (n - 1) x)
          =
        244 * (2 * (2 : ℤ)^(S (n - 1) x)) := by
          ring
      _ =
        244 * lemma_1J_L n x := by
          rw [h]

  have h_pen_bound :
      244 * lemma_1J_visible_term n x (n - 1) =
        183 * lemma_1J_L n x := by
    rw [h_pen_visible]

    have h :=
      lemma_1J_penultimate_visible_four_eq_three_L n x floor h_rep

    calc
      244 * ((3 : ℤ) * (2 : ℤ)^(S (n - 2) x))
          =
        61 * (4 * ((3 : ℤ) * (2 : ℤ)^(S (n - 2) x))) := by
          ring
      _ =
        61 * (3 * lemma_1J_L n x) := by
          rw [h]
      _ =
        183 * lemma_1J_L n x := by
          ring

  have h_earlier_bound :
      244 *
          (∑ k ∈ Ico (q + 2) (n - 1),
            lemma_1J_visible_term n x k)
        ≤
      9 * lemma_1J_L n x := by
    dsimp [q]
    exact lemma_1J_earlier_visible_tail_bound n x floor h_rep

  have h_visible_bound :
      244 *
        (∑ k ∈ Ico (q + 2) (n + 1),
          lemma_1J_visible_term n x k)
      ≤
      314 * lemma_1J_L n x := by
    rw [h_split]
    nlinarith [h_earlier_bound, h_pen_bound, h_final_bound]

  have h_gp2_scaled :
      244 * lemma_1J_GP2 n x floor <
        244 *
          (∑ k ∈ Ico (q + 2) (n + 1),
            lemma_1J_visible_term n x k) := by
    have h244_pos : (0 : ℤ) < 244 := by norm_num
    exact mul_lt_mul_of_pos_left h_gp2_visible h244_pos

  linarith

#check lemma_1J_GP2_lt_visible_sum
#check lemma_1J_GP2_bound

/--
Lemma 1J, index shift between the existing `delta_N_actual_inc` terms and
the manuscript `T_k` terms.

The codebase uses index `j`; Lemma 1J uses `k = j + 1`.
-/
lemma lemma_1J_delta_term_shift
  (n x j : ℕ)
  (hj : j ∈ Ico 1 n) :
  (3 : ℤ)^(n - 1 - j) *
      ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j))
    =
  lemma_1J_T n x (j + 1) := by

  unfold lemma_1J_T

  have h_pred :
      j + 1 - 1 = j := by
    omega

  have h_three :
      n - (j + 1) = n - 1 - j := by
    rw [mem_Ico] at hj
    omega

  have h_two :
      2 * (j + 1) - 2 = 2 * j := by
    omega

  rw [h_pred, h_three, h_two]

/--
Lemma 1J, actual numerator deviation as the manuscript `T_k` sum.

This derives

`ΔN_actual = sum_{k=1}^n T_k`.

The extra `k = 1` term is zero.
-/
lemma lemma_1J_delta_actual_as_T_sum
  (n x : ℕ) :
  delta_N_actual_inc n x =
    ∑ k ∈ Ico 1 (n + 1), lemma_1J_T n x k := by

  by_cases hn_zero : n = 0

  · subst n
    unfold delta_N_actual_inc lemma_1J_T
    simp

  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn_zero

    unfold delta_N_actual_inc

    have h_shift :
        (∑ j ∈ Ico 1 n,
          (3 : ℤ)^(n - 1 - j) *
            ((2 : ℤ)^(S j x) - (2 : ℤ)^(2 * j)))
        =
        ∑ j ∈ Ico 1 n, lemma_1J_T n x (j + 1) := by
      apply sum_congr rfl
      intro j hj
      exact lemma_1J_delta_term_shift n x j hj

    rw [h_shift]

    have h_map :
        ∑ j ∈ Ico 1 n, lemma_1J_T n x (j + 1)
          =
        ∑ k ∈ Ico 2 (n + 1), lemma_1J_T n x k := by
      have h_image :
          (Ico 1 n).image (fun j => j + 1) = Ico 2 (n + 1) := by
        ext k
        rw [mem_image]
        constructor

        · intro hk
          rcases hk with ⟨j, hj, hjk⟩
          subst k
          rw [mem_Ico] at hj ⊢
          omega

        · intro hk
          rw [mem_Ico] at hk
          refine ⟨k - 1, ?_, ?_⟩

          · rw [mem_Ico]
            omega

          · omega

      rw [← h_image]
      rw [sum_image]

      intro a ha b hb hab
      exact Nat.add_right_cancel hab

    rw [h_map]

    have h_one_mem :
        1 ∈ Ico 1 (n + 1) := by
      rw [mem_Ico]
      omega

    have h_erase :
        (Ico 1 (n + 1)).erase 1 = Ico 2 (n + 1) := by
      ext k
      rw [mem_erase, mem_Ico, mem_Ico]
      constructor

      · intro hk
        exact ⟨by omega, hk.2.2⟩

      · intro hk
        exact ⟨by omega, by omega, hk.2⟩

    rw [← h_erase]

    calc
      ∑ k ∈ (Ico 1 (n + 1)).erase 1, lemma_1J_T n x k
          =
        (∑ k ∈ (Ico 1 (n + 1)).erase 1, lemma_1J_T n x k) +
          lemma_1J_T n x 1 := by
          rw [lemma_1J_T_one_zero]
          ring
      _ =
        ∑ k ∈ Ico 1 (n + 1), lemma_1J_T n x k := by
          rw [sum_erase_add _ _ h_one_mem]

/--
Lemma 1J, decomposition of the actual numerator deviation.

This is the manuscript split

`ΔN_actual = GP_1 + T_{q+1} + GP_2`.
-/
lemma lemma_1J_delta_actual_decomposition
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  delta_N_actual_inc n x =
    lemma_1J_GP1 n x floor +
      lemma_1J_T n x (lemma_1J_bridge_index n floor + 1) +
        lemma_1J_GP2 n x floor := by

  rcases h_rep with
    ⟨_, _, h_tail_end, _, _, _, _, _, _, _⟩

  let q := lemma_1J_bridge_index n floor

  rw [lemma_1J_delta_actual_as_T_sum]

  unfold lemma_1J_GP1
  unfold lemma_1J_GP2

  change
    (∑ k ∈ Ico 1 (n + 1), lemma_1J_T n x k) =
      (∑ k ∈ Ico 1 (q + 1), lemma_1J_T n x k) +
        lemma_1J_T n x (q + 1) +
          ∑ k ∈ Ico (q + 2) (n + 1), lemma_1J_T n x k

  have h_bridge_mem :
      q + 1 ∈ Ico 1 (n + 1) := by
    rw [mem_Ico]
    omega

  rw [← sum_erase_add _ _ h_bridge_mem]

  have h_erase_bridge :
      (Ico 1 (n + 1)).erase (q + 1) =
        Ico 1 (q + 1) ∪ Ico (q + 2) (n + 1) := by
    ext k
    rw [mem_erase, mem_union, mem_Ico, mem_Ico, mem_Ico]
    constructor

    · intro hk
      have hk_ne : k ≠ q + 1 := hk.1
      have hk_bounds : 1 ≤ k ∧ k < n + 1 := hk.2

      by_cases h_left : k < q + 1

      · exact Or.inl ⟨hk_bounds.1, h_left⟩

      · right
        exact ⟨by omega, hk_bounds.2⟩

    · intro hk
      rcases hk with hk_left | hk_right

      · exact ⟨by omega, ⟨hk_left.1, by omega⟩⟩

      · exact ⟨by omega, ⟨by omega, hk_right.2⟩⟩

  rw [h_erase_bridge]
  rw [sum_union]

  · ring

  · rw [disjoint_left]
    intro k hk_left hk_right
    rw [mem_Ico] at hk_left hk_right
    omega

#check lemma_1J_delta_term_shift
#check lemma_1J_delta_actual_as_T_sum
#check lemma_1J_delta_actual_decomposition

/--
Lemma 1J, actual numerator-deviation bound.

From

`ΔN_actual = GP_1 + T_{q+1} + GP_2`,

with `GP_1 < 0` and `T_{q+1} < 0`, the actual deviation is bounded by
`GP_2`, hence by the GP2 ceiling.

This is the manuscript bound

`ΔN_actual < 157/122 * L`,

encoded without division as

`244 * ΔN_actual < 314 * L`.
-/
lemma lemma_1J_delta_actual_bound
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  244 * delta_N_actual_inc n x <
    314 * lemma_1J_L n x := by

  have h_delta_decomp :
      delta_N_actual_inc n x =
        lemma_1J_GP1 n x floor +
          lemma_1J_T n x (lemma_1J_bridge_index n floor + 1) +
            lemma_1J_GP2 n x floor :=
    lemma_1J_delta_actual_decomposition n x floor h_rep

  have h_gp1_neg :
      lemma_1J_GP1 n x floor < 0 :=
    lemma_1J_GP1_neg n x floor h_rep

  have h_bridge_neg :
      lemma_1J_T n x (lemma_1J_bridge_index n floor + 1) < 0 :=
    lemma_1J_T_bridge_neg n x floor h_rep

  have h_gp2_bound :
      244 * lemma_1J_GP2 n x floor <
        314 * lemma_1J_L n x :=
    lemma_1J_GP2_bound n x floor h_rep

  have h_delta_lt_gp2 :
      delta_N_actual_inc n x < lemma_1J_GP2 n x floor := by
    rw [h_delta_decomp]
    linarith

  have h_scaled :
      244 * delta_N_actual_inc n x <
        244 * lemma_1J_GP2 n x floor := by
    exact mul_lt_mul_of_pos_left h_delta_lt_gp2 (by norm_num : (0 : ℤ) < 244)

  linarith

#check lemma_1J_delta_actual_bound
/--
Lemma 1J, numerator decomposition.

This is the manuscript identity

`N_new = N_eq + ΔN_actual`.

In the codebase, `N_new` is `sum_T`.
-/
lemma lemma_1J_sum_T_eq_Neq_plus_delta
  (n x : ℕ)
  (hn : 0 < n) :
  (sum_T n x : ℤ) =
    (N_eq n : ℤ) + delta_N_actual_inc n x := by

  have h_delta :
      (sum_T n x : ℤ) - (N_eq n : ℤ) =
        delta_N_actual_inc n x :=
    lemma_delta_equiv_bridge n x hn

  omega

/--
Lemma 1J, equilibrium numerator is below `L`.

Since `N_eq = 2^(2n)-3^n < 2^(2n)` and `S_n ≥ 2n`, we have

`N_eq < L`.
-/
lemma lemma_1J_Neq_lt_L
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  (N_eq n : ℤ) < lemma_1J_L n x := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨h_floor, _, _, _, _, _, _, _, _, _⟩

  have hS :
      S n x = 2 * n - 2 + 2 * 3^(floor - 2) :=
    lemma_1J_total_exponent n x floor h_rep_copy

  have hS_ge :
      2 * n ≤ S n x := by
    rw [hS]

    have h_pow_ge_one :
        1 ≤ 3^(floor - 2) := by
      exact Nat.one_le_pow _ _ (by norm_num)

    have h_extra_ge_two :
        2 ≤ 2 * 3^(floor - 2) := by
      calc
        2 = 2 * 1 := by
          norm_num
        _ ≤ 2 * 3^(floor - 2) := by
          exact Nat.mul_le_mul_left 2 h_pow_ge_one

    have h_rewrite :
        2 * n - 2 + 2 * 3^(floor - 2) =
          2 * n + (2 * 3^(floor - 2) - 2) := by
      omega

    rw [h_rewrite]
    omega
  have h_pow_ge :
      (2 : ℤ)^(2 * n) ≤ (2 : ℤ)^(S n x) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hS_ge

  have h_Neq_int :
      (N_eq n : ℤ) = (2 : ℤ)^(2 * n) - (3 : ℤ)^n :=
    N_eq_int n

  unfold lemma_1J_L
  rw [h_Neq_int]

  have h_three_pos :
      0 < (3 : ℤ)^n := by
    positivity

  linarith

/--
Lemma 1J, numerator ceiling.

Combining

`N_new = N_eq + ΔN_actual`,
`N_eq < L`, and
`ΔN_actual < 157/122 L`

gives

`N_new < 279/122 L`.

Encoded without division:

`122 * N_new < 279 * L`.
-/
lemma lemma_1J_sum_T_bound
  (n x floor : ℕ)
  (hn : 0 < n)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  122 * (sum_T n x : ℤ) <
    279 * lemma_1J_L n x := by

  have h_sum :
      (sum_T n x : ℤ) =
        (N_eq n : ℤ) + delta_N_actual_inc n x :=
    lemma_1J_sum_T_eq_Neq_plus_delta n x hn

  have h_Neq :
      (N_eq n : ℤ) < lemma_1J_L n x :=
    lemma_1J_Neq_lt_L n x floor h_rep

  have h_delta :
      244 * delta_N_actual_inc n x <
        314 * lemma_1J_L n x :=
    lemma_1J_delta_actual_bound n x floor h_rep

  rw [h_sum]

  have h_Neq_scaled :
      122 * (N_eq n : ℤ) < 122 * lemma_1J_L n x := by
    exact mul_lt_mul_of_pos_left h_Neq (by norm_num : (0 : ℤ) < 122)

  have h_delta_half :
      122 * delta_N_actual_inc n x <
        157 * lemma_1J_L n x := by
    nlinarith [h_delta]

  nlinarith

#check lemma_1J_sum_T_eq_Neq_plus_delta
#check lemma_1J_Neq_lt_L
#check lemma_1J_sum_T_bound

/--
Lemma 1J, the genuine lifted representative has length at least five.
-/
lemma lemma_1J_n_ge_five
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  5 ≤ n := by

  rcases h_rep with
    ⟨_, hq_ge, h_tail_end, _, _, _, _, _, _, _⟩

  have hq_pos :
      2 ≤ lemma_1J_bridge_index n floor := hq_ge

  have h_tail :
      lemma_1J_bridge_index n floor + 1 ≤ n - 2 := h_tail_end

  omega

/--
Lemma 1J, total exponent is at least equilibrium size.

From

`S_n = 2n - 2 + 2*3^(floor-2)`

and `floor ≥ 2`, we get `2n ≤ S_n`.
-/
lemma lemma_1J_total_exponent_ge_equilibrium
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  2 * n ≤ S n x := by

  have h_rep_copy := h_rep

  rcases h_rep with
    ⟨h_floor, _, _, _, _, _, _, _, _, _⟩

  have hS :
      S n x = 2 * n - 2 + 2 * 3^(floor - 2) :=
    lemma_1J_total_exponent n x floor h_rep_copy

  rw [hS]

  have h_pow_ge_one :
      1 ≤ 3^(floor - 2) := by
    exact Nat.one_le_pow _ _ (by norm_num)

  have h_extra_ge_two :
      2 ≤ 2 * 3^(floor - 2) := by
    calc
      2 = 2 * 1 := by
        norm_num
      _ ≤ 2 * 3^(floor - 2) := by
        exact Nat.mul_le_mul_left 2 h_pow_ge_one

  have h_rewrite :
      2 * n - 2 + 2 * 3^(floor - 2) =
        2 * n + (2 * 3^(floor - 2) - 2) := by
    omega

  rw [h_rewrite]
  omega

/--
Lemma 1J, denominator lower bound.

The manuscript bound

`D_new = L - 3^n > 3L/4`

is encoded without division as

`3L < 4 * D_new`.
-/
lemma lemma_1J_denominator_lower_bound
  (n x floor : ℕ)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  3 * lemma_1J_L n x <
    4 * (((2 : ℤ)^(S n x) - (3 : ℤ)^n)) := by

  have hn_ge_five :
      5 ≤ n :=
    lemma_1J_n_ge_five n x floor h_rep

  have hS_ge :
      2 * n ≤ S n x :=
    lemma_1J_total_exponent_ge_equilibrium n x floor h_rep

  have h_pow2_ge :
      (2 : ℤ)^(2 * n) ≤ (2 : ℤ)^(S n x) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hS_ge

  have h_three_four :
      4 * (3 : ℤ)^n < (2 : ℤ)^(2 * n) := by
    have h_nat :
        4 * 3^n < 2^(2 * n) := by
      have h_core :
          ∀ t : ℕ, 972 * 3^t < 1024 * 4^t := by
        intro t
        induction t with
        | zero =>
            norm_num
        | succ t ih =>
            calc
              972 * 3^(t + 1)
                  = 3 * (972 * 3^t) := by ring
              _ < 3 * (1024 * 4^t) := by
                  exact Nat.mul_lt_mul_of_pos_left ih (by norm_num)
              _ ≤ 4 * (1024 * 4^t) := by
                  exact Nat.mul_le_mul_right (1024 * 4^t) (by norm_num : 3 ≤ 4)
              _ = 1024 * 4^(t + 1) := by ring

      let t := n - 5

      have hn_eq :
          n = t + 5 := by
        dsimp [t]
        omega

      rw [hn_eq]

      have h_left :
          4 * 3^(t + 5) = 972 * 3^t := by
        rw [pow_add]
        norm_num
        ring

      have h_right :
          2^(2 * (t + 5)) = 1024 * 4^t := by
        have h_exp :
            2 * (t + 5) = 2 * t + 10 := by
          omega
        rw [h_exp, pow_add]

        have h_two :
            2^(2 * t) = 4^t := by
          rw [pow_mul]
          norm_num

        rw [h_two]
        norm_num
        ring

      rw [h_left, h_right]
      exact h_core t

    exact_mod_cast h_nat

  have h_three_L :
      4 * (3 : ℤ)^n < lemma_1J_L n x := by
    unfold lemma_1J_L
    exact lt_of_lt_of_le h_three_four h_pow2_ge

  unfold lemma_1J_L at h_three_L ⊢
  linarith

#check lemma_1J_n_ge_five
#check lemma_1J_total_exponent_ge_equilibrium
#check lemma_1J_denominator_lower_bound
/--
Lemma 1J, cycle-level ratio ceiling for the minimal-lift representative.

For a cycle satisfying the Lemma 1J representative profile, the cycle ratio
`x` is strictly below `5`.
-/
lemma lemma_1J_cycle_ratio_lt_five
  (n x floor : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  x < 5 := by

  have h_num :
      122 * (sum_T n x : ℤ) <
        279 * lemma_1J_L n x :=
    lemma_1J_sum_T_bound n x floor hn h_rep

  have h_den :
      3 * lemma_1J_L n x <
        4 * (((2 : ℤ)^(S n x) - (3 : ℤ)^n)) :=
    lemma_1J_denominator_lower_bound n x floor h_rep

  have h_cycle_eq :
      (sum_T n x : ℤ) =
        (x : ℤ) * (((2 : ℤ)^(S n x) - (3 : ℤ)^n)) := by
    calc
      (sum_T n x : ℤ)
          =
        (2 : ℤ)^(S n x) * (x : ℤ) -
          (3 : ℤ)^n * (x : ℤ) :=
        cycle_diophantine_int n x h_cycle hn
      _ =
        (x : ℤ) * (((2 : ℤ)^(S n x) - (3 : ℤ)^n)) := by
        ring

  let D : ℤ := (2 : ℤ)^(S n x) - (3 : ℤ)^n
  let L : ℤ := lemma_1J_L n x

  have h_num_D :
      122 * ((x : ℤ) * D) < 279 * L := by
    dsimp [D, L]
    rw [← h_cycle_eq]
    exact h_num

  have h_den_D :
      3 * L < 4 * D := by
    dsimp [D, L]
    exact h_den

  have hD_pos : 0 < D := by
    have hL_pos : 0 < L := by
      dsimp [L, lemma_1J_L]
      positivity
    nlinarith

  have h_x_scaled :
      366 * (x : ℤ) * D < 1116 * D := by
    nlinarith [h_num_D, h_den_D]

  have h_x_int :
      (x : ℤ) < 4 := by
    have hD_nonneg : 0 ≤ D := hD_pos.le

    have h_cancel :
        366 * (x : ℤ) < 1116 := by
      exact lt_of_mul_lt_mul_right h_x_scaled hD_nonneg

    nlinarith

  have hx_lt_four :
      x < 4 := by
    exact_mod_cast h_x_int

  omega

#check lemma_1J_cycle_ratio_lt_five

/--
Lemma 1J, cycle-facing closure.

The maximal-ratio minimal-lift representative cannot occur in a nontrivial
positive integer cycle. Lemma 1J gives `x < 5`, while Constraint 3 gives
`5 ≤ x`.
-/
theorem lemma_1J_minimal_lift_representative_cycle_closed
  (n x floor : ℕ)
  (h_cycle : is_cycle n x)
  (hn : 0 < n)
  (hx : x > 1)
  (h_rep : lemma_1J_minimal_lift_representative n x floor) :
  False := by

  have h_lt :
      x < 5 :=
    lemma_1J_cycle_ratio_lt_five n x floor h_cycle hn h_rep

  have h_ge :
      5 ≤ x :=
    constraint_3_nontrivial_cycle_ratio_ge_five n x h_cycle hn hx

  omega

#check lemma_1J_minimal_lift_representative_cycle_closed
#print axioms lemma_1J_minimal_lift_representative_cycle_closed

-- ===============================================================
-- SECTION 23: LEMMA 1K (POSITIVE EXPONENT INFLATION)
-- ===============================================================

section Section23_Lemma1K_Positive_Inflation

/--
Lemma 1K, profile prefix sum.

For an exponent profile `a`, this is the manuscript prefix

`S_j = a_1 + ... + a_j`.

Lean uses zero-indexing, so this is `sum_{i=0}^{j-1} a_i`.
-/
def lemma_1K_prefix_sum
  (a : ℕ → ℕ)
  (j : ℕ) : ℕ :=
  ∑ i ∈ range j, a i

/--
Lemma 1K, profile total exponent sum.

This is the manuscript total `S = S_n`.
-/
def lemma_1K_total_sum
  (n : ℕ)
  (a : ℕ → ℕ) : ℕ :=
  lemma_1K_prefix_sum a n

/--
Lemma 1K, profile numerator.

This is

`N(a) = sum_{j=0}^{n-1} 3^(n-1-j) * 2^(S_j)`.
-/
def lemma_1K_N
  (n : ℕ)
  (a : ℕ → ℕ) : ℤ :=
  ∑ j ∈ range n,
    (3 : ℤ)^(n - 1 - j) *
      (2 : ℤ)^(lemma_1K_prefix_sum a j)

/--
Lemma 1K, profile denominator.

This is

`D(a) = 2^S - 3^n`.
-/
def lemma_1K_D
  (n : ℕ)
  (a : ℕ → ℕ) : ℤ :=
  (2 : ℤ)^(lemma_1K_total_sum n a) - (3 : ℤ)^n

/--
Lemma 1K, total inflation gap.

This is the manuscript quantity

`R = S_hat - S`.
-/
def lemma_1K_R
  (n : ℕ)
  (a ahat : ℕ → ℕ) : ℕ :=
  lemma_1K_total_sum n ahat - lemma_1K_total_sum n a

/--
Lemma 1K, componentwise positive exponent inflation.

The inflated profile satisfies `ahat_i ≥ a_i` for every visible exponent,
with at least one strict inequality.
-/
def lemma_1K_componentwise_positive_inflation
  (n : ℕ)
  (a ahat : ℕ → ℕ) : Prop :=
  (∀ i < n, a i ≤ ahat i) ∧
    ∃ i < n, a i < ahat i

#check lemma_1K_prefix_sum
#check lemma_1K_total_sum
#check lemma_1K_N
#check lemma_1K_D
#check lemma_1K_R
#check lemma_1K_componentwise_positive_inflation
/--
Lemma 1K, prefix sums are monotone under componentwise inflation.
-/
lemma lemma_1K_prefix_sum_le
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (j : ℕ)
  (hj : j ≤ n) :
  lemma_1K_prefix_sum a j ≤ lemma_1K_prefix_sum ahat j := by

  unfold lemma_1K_prefix_sum

  apply sum_le_sum
  intro i hi

  have hi_lt_j :
      i < j := by
    simpa using mem_range.mp hi

  exact h_inf.1 i (by omega)

/--
Lemma 1K, total sum is monotone under componentwise inflation.
-/
lemma lemma_1K_total_sum_le
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  lemma_1K_total_sum n a ≤ lemma_1K_total_sum n ahat := by

  unfold lemma_1K_total_sum
  exact lemma_1K_prefix_sum_le n a ahat h_inf n (by omega)

/--
Lemma 1K, positive inflation gives a strictly positive total gap.
-/
lemma lemma_1K_total_sum_lt
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  lemma_1K_total_sum n a < lemma_1K_total_sum n ahat := by

  rcases h_inf with ⟨h_le, i, hi_lt, h_strict⟩

  unfold lemma_1K_total_sum
  unfold lemma_1K_prefix_sum

  have h_i_mem :
      i ∈ range n := by
    exact mem_range.mpr hi_lt

  have h_sum_le :
      ∑ k ∈ (range n).erase i, a k ≤
        ∑ k ∈ (range n).erase i, ahat k := by
    apply sum_le_sum
    intro k hk

    have hk_mem :
        k ∈ range n := (mem_erase.mp hk).2

    exact h_le k (mem_range.mp hk_mem)

  rw [← sum_erase_add _ _ h_i_mem]
  rw [← sum_erase_add _ _ h_i_mem]

  omega

/--
Lemma 1K, the total inflation gap is positive.
-/
lemma lemma_1K_R_pos
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  0 < lemma_1K_R n a ahat := by

  unfold lemma_1K_R

  have h_lt :
      lemma_1K_total_sum n a < lemma_1K_total_sum n ahat :=
    lemma_1K_total_sum_lt n a ahat h_inf

  omega

/--
Lemma 1K, total sum decomposes through the inflation gap.

`S_hat = S + R`.
-/
lemma lemma_1K_total_sum_add_R
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  lemma_1K_total_sum n ahat =
    lemma_1K_total_sum n a + lemma_1K_R n a ahat := by

  unfold lemma_1K_R

  have h_le :
      lemma_1K_total_sum n a ≤ lemma_1K_total_sum n ahat :=
    lemma_1K_total_sum_le n a ahat h_inf

  omega

/--
Lemma 1K, prefix inflation is bounded by the total inflation gap.

For `j ≤ n`,

`S_hat_j - S_j ≤ R`.
-/
lemma lemma_1K_prefix_gap_le_R
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (j : ℕ)
  (hj : j ≤ n) :
  lemma_1K_prefix_sum ahat j - lemma_1K_prefix_sum a j
    ≤
  lemma_1K_R n a ahat := by

  unfold lemma_1K_R
  unfold lemma_1K_total_sum

  unfold lemma_1K_prefix_sum

  have h_decomp_a :
      ∑ i ∈ range n, a i =
        (∑ i ∈ range j, a i) +
          ∑ i ∈ Ico j n, a i := by
    rw [← sum_range_add_sum_Ico]
    omega

  have h_decomp_ahat :
      ∑ i ∈ range n, ahat i =
        (∑ i ∈ range j, ahat i) +
          ∑ i ∈ Ico j n, ahat i := by
    rw [← sum_range_add_sum_Ico]
    omega

  have h_tail_le :
      ∑ i ∈ Ico j n, a i ≤
        ∑ i ∈ Ico j n, ahat i := by
    apply sum_le_sum
    intro i hi

    have hi_lt :
        i < n := (mem_Ico.mp hi).2

    exact h_inf.1 i hi_lt

  omega

#check lemma_1K_prefix_sum_le
#check lemma_1K_total_sum_le
#check lemma_1K_total_sum_lt
#check lemma_1K_R_pos
#check lemma_1K_total_sum_add_R
#check lemma_1K_prefix_gap_le_R
/--
Lemma 1K, prefix power inflation bound.

For every `j ≤ n`, the inflated prefix power is bounded by the original prefix
power times the global inflation factor:

`2^(S_hat_j) ≤ 2^R * 2^(S_j)`.
-/
lemma lemma_1K_prefix_power_bound
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (j : ℕ)
  (hj : j ≤ n) :
  (2 : ℤ)^(lemma_1K_prefix_sum ahat j) ≤
    (2 : ℤ)^(lemma_1K_R n a ahat) *
      (2 : ℤ)^(lemma_1K_prefix_sum a j) := by

  have h_prefix_le :
      lemma_1K_prefix_sum a j ≤ lemma_1K_prefix_sum ahat j :=
    lemma_1K_prefix_sum_le n a ahat h_inf j hj

  have h_gap_le :
      lemma_1K_prefix_sum ahat j - lemma_1K_prefix_sum a j
        ≤
      lemma_1K_R n a ahat :=
    lemma_1K_prefix_gap_le_R n a ahat h_inf j hj

  have h_decomp :
      lemma_1K_prefix_sum ahat j =
        lemma_1K_prefix_sum a j +
          (lemma_1K_prefix_sum ahat j -
            lemma_1K_prefix_sum a j) := by
    omega

  rw [h_decomp]
  rw [pow_add]

  have h_pow_gap :
      (2 : ℤ)^(lemma_1K_prefix_sum ahat j -
          lemma_1K_prefix_sum a j)
        ≤
      (2 : ℤ)^(lemma_1K_R n a ahat) := by
    exact pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) h_gap_le

  nlinarith [
    mul_le_mul_of_nonneg_right
      h_pow_gap
      (by positivity :
        0 ≤ (2 : ℤ)^(lemma_1K_prefix_sum a j))
  ]

/--
Lemma 1K, numerator inflation bound.

The numerator grows by at most the global factor `2^R`:

`N(ahat) ≤ 2^R * N(a)`.
-/
lemma lemma_1K_numerator_bound
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  lemma_1K_N n ahat ≤
    (2 : ℤ)^(lemma_1K_R n a ahat) * lemma_1K_N n a := by

  unfold lemma_1K_N

  rw [mul_sum]

  apply sum_le_sum
  intro j hj

  have hj_le :
      j ≤ n := by
    exact Nat.le_of_lt (mem_range.mp hj)

  have h_prefix_power :
      (2 : ℤ)^(lemma_1K_prefix_sum ahat j) ≤
        (2 : ℤ)^(lemma_1K_R n a ahat) *
          (2 : ℤ)^(lemma_1K_prefix_sum a j) :=
    lemma_1K_prefix_power_bound n a ahat h_inf j hj_le

  have h_three_nonneg :
      0 ≤ (3 : ℤ)^(n - 1 - j) := by
    positivity

  have h_scaled :
      (3 : ℤ)^(n - 1 - j) *
          (2 : ℤ)^(lemma_1K_prefix_sum ahat j)
        ≤
      (3 : ℤ)^(n - 1 - j) *
        ((2 : ℤ)^(lemma_1K_R n a ahat) *
          (2 : ℤ)^(lemma_1K_prefix_sum a j)) := by
    exact mul_le_mul_of_nonneg_left h_prefix_power h_three_nonneg

  ring_nf at h_scaled ⊢
  exact h_scaled

#check lemma_1K_prefix_power_bound
#check lemma_1K_numerator_bound
/--
Lemma 1K, denominator expansion under inflation.

This is the manuscript identity

`D(ahat) = 2^R D(a) + (2^R - 1) * 3^n`.
-/
lemma lemma_1K_denominator_expansion
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat) :
  lemma_1K_D n ahat =
    (2 : ℤ)^(lemma_1K_R n a ahat) * lemma_1K_D n a +
      ((2 : ℤ)^(lemma_1K_R n a ahat) - 1) *
        (3 : ℤ)^n := by

  have h_total :
      lemma_1K_total_sum n ahat =
        lemma_1K_total_sum n a + lemma_1K_R n a ahat :=
    lemma_1K_total_sum_add_R n a ahat h_inf

  unfold lemma_1K_D

  rw [h_total]
  rw [pow_add]
  ring

/--
Lemma 1K, denominator grows by more than the global factor.

If `D(a) > 0`, then

`D(ahat) > 2^R * D(a)`.
-/
lemma lemma_1K_denominator_strict_growth
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (_hD_pos : 0 < lemma_1K_D n a) :
  (2 : ℤ)^(lemma_1K_R n a ahat) * lemma_1K_D n a <
    lemma_1K_D n ahat := by

  rw [lemma_1K_denominator_expansion n a ahat h_inf]

  have hR_pos :
      0 < lemma_1K_R n a ahat :=
    lemma_1K_R_pos n a ahat h_inf

  have h_two_pow_gt_one :
      1 < (2 : ℤ)^(lemma_1K_R n a ahat) := by
    have h_ne_zero :
        lemma_1K_R n a ahat ≠ 0 := by
      omega

    cases hR : lemma_1K_R n a ahat with
    | zero =>
        exact False.elim (h_ne_zero hR)
    | succ r =>
        rw [pow_succ]

        have h_pow_pos :
            0 < (2 : ℤ)^r := by
          positivity

        nlinarith

  have h_extra_pos :
      0 <
        ((2 : ℤ)^(lemma_1K_R n a ahat) - 1) *
          (3 : ℤ)^n := by
    have h_left_pos :
        0 < (2 : ℤ)^(lemma_1K_R n a ahat) - 1 := by
      linarith

    have h_right_pos :
        0 < (3 : ℤ)^n := by
      positivity

    exact mul_pos h_left_pos h_right_pos

  linarith

#check lemma_1K_denominator_expansion
#check lemma_1K_denominator_strict_growth
/--
Lemma 1K, positive exponent inflation decreases the cycle ratio.

This is the division-free form of

`N(ahat) / D(ahat) < N(a) / D(a)`,

under the manuscript hypothesis `D(a) > 0`.
-/
theorem lemma_1K_positive_inflation_decreases_ratio
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (hD_pos : 0 < lemma_1K_D n a) :
  lemma_1K_N n ahat * lemma_1K_D n a <
    lemma_1K_N n a * lemma_1K_D n ahat := by

  let F : ℤ := (2 : ℤ)^(lemma_1K_R n a ahat)

  have hN_bound :
      lemma_1K_N n ahat ≤
        F * lemma_1K_N n a := by
    dsimp [F]
    exact lemma_1K_numerator_bound n a ahat h_inf

  have hD_growth :
      F * lemma_1K_D n a <
        lemma_1K_D n ahat := by
    dsimp [F]
    exact lemma_1K_denominator_strict_growth n a ahat h_inf hD_pos

  have hn_pos :
      0 < n := by
    by_contra h_not
    have hn_zero : n = 0 := by
      omega
    subst n
    unfold lemma_1K_D lemma_1K_total_sum lemma_1K_prefix_sum at hD_pos
    simp at hD_pos

  have hN_pos :
      0 < lemma_1K_N n a := by
    unfold lemma_1K_N

    have h_zero_mem :
        0 ∈ range n := by
      exact mem_range.mpr hn_pos

    rw [← sum_erase_add _ _ h_zero_mem]

    have h_rest_nonneg :
        0 ≤
          ∑ j ∈ (range n).erase 0,
            (3 : ℤ)^(n - 1 - j) *
              (2 : ℤ)^(lemma_1K_prefix_sum a j) := by
      apply sum_nonneg
      intro j hj
      positivity

    have h_zero_term_pos :
        0 <
          (3 : ℤ)^(n - 1 - 0) *
            (2 : ℤ)^(lemma_1K_prefix_sum a 0) := by
      positivity

    linarith

  have hD_nonneg :
      0 ≤ lemma_1K_D n a := by
    exact hD_pos.le

  have h_left_le :
      lemma_1K_N n ahat * lemma_1K_D n a ≤
        (F * lemma_1K_N n a) * lemma_1K_D n a := by
    exact mul_le_mul_of_nonneg_right hN_bound hD_nonneg

  have h_right_lt :
      (F * lemma_1K_N n a) * lemma_1K_D n a <
        lemma_1K_N n a * lemma_1K_D n ahat := by

    have h_scaled :
        lemma_1K_N n a * (F * lemma_1K_D n a) <
          lemma_1K_N n a * lemma_1K_D n ahat := by
      exact mul_lt_mul_of_pos_left hD_growth hN_pos

    nlinarith

  exact lt_of_le_of_lt h_left_le h_right_lt

#check lemma_1K_positive_inflation_decreases_ratio
#print axioms lemma_1K_positive_inflation_decreases_ratio

end Section23_Lemma1K_Positive_Inflation
/--
Lemma 1K, rational ratio form.

This is the manuscript inequality

`N(ahat) / D(ahat) < N(a) / D(a)`

obtained from the division-free cross-product theorem.
-/
theorem lemma_1K_positive_inflation_decreases_ratio_rat
  (n : ℕ)
  (a ahat : ℕ → ℕ)
  (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
  (hD_pos : 0 < lemma_1K_D n a) :
  ((lemma_1K_N n ahat : ℚ) / (lemma_1K_D n ahat : ℚ)) <
    ((lemma_1K_N n a : ℚ) / (lemma_1K_D n a : ℚ)) := by

  let F : ℤ := (2 : ℤ)^(lemma_1K_R n a ahat)

  have hD_growth :
      F * lemma_1K_D n a < lemma_1K_D n ahat := by
    dsimp [F]
    exact lemma_1K_denominator_strict_growth n a ahat h_inf hD_pos

  have hF_pos :
      0 < F := by
    dsimp [F]
    positivity

  have hDhat_pos_int :
      0 < lemma_1K_D n ahat := by
    exact lt_trans (mul_pos hF_pos hD_pos) hD_growth

  have hD_pos_rat :
      (0 : ℚ) < (lemma_1K_D n a : ℚ) := by
    exact_mod_cast hD_pos

  have hDhat_pos_rat :
      (0 : ℚ) < (lemma_1K_D n ahat : ℚ) := by
    exact_mod_cast hDhat_pos_int

  have h_cross_int :
      lemma_1K_N n ahat * lemma_1K_D n a <
        lemma_1K_N n a * lemma_1K_D n ahat :=
    lemma_1K_positive_inflation_decreases_ratio
      n a ahat h_inf hD_pos

  have h_cross_rat :
      ((lemma_1K_N n ahat : ℚ) * (lemma_1K_D n a : ℚ)) <
        ((lemma_1K_N n a : ℚ) * (lemma_1K_D n ahat : ℚ)) := by
    exact_mod_cast h_cross_int

  field_simp
    [ne_of_gt hD_pos_rat, ne_of_gt hDhat_pos_rat]

  simpa [mul_comm] using h_cross_rat

#check lemma_1K_positive_inflation_decreases_ratio_rat
#print axioms lemma_1K_positive_inflation_decreases_ratio_rat

section Theorem1_Pure_Positive_Branch

/--
Unconditional closure of the pure positive branch (first component of Theorem 1).

Lemma 1D (`Lemma_1D_Final_Comparison`) shows that any purely positive perturbation forces
the denominator `D = 2^S - 3^n` to strictly exceed the numerator `N = sum_T`, i.e.
`0 < Z = N/D < 1`.  Combined with the cycle Diophantine identity `D · x = N` (recall the
seed `x` plays the role of the ratio `Z`), this makes an integer cycle ratio impossible.
-/
theorem theorem_1_pure_positive_branch_closed
    (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n)
    (h_pos : is_pure_positive n x) : False := by
  -- Lemma 1D over ℚ:  N < D.
  have h1D := Lemma_1D_Final_Comparison n x h_pos
  -- Cycle Diophantine identity over ℕ:  (2^S - 3^n) · x = N.
  have h_dioph := cycle_implies_explicit_diophantine n x h_cycle
  -- Existence threshold:  3^n < 2^S, hence D > 0.
  have h_thr := cycle_existence_threshold n x h_cycle hn
  -- The cycle seed is odd, hence at least 1.
  have h_odd := cycle_implies_odd n x h_cycle hn
  have hx1 : 1 ≤ x := by omega
  have hle : (3 : ℕ) ^ n ≤ 2 ^ (S n x) := le_of_lt h_thr
  -- Cast the (truncated) ℕ denominator to the genuine ℚ difference.
  have hcast : ((2 ^ (S n x) - 3 ^ n : ℕ) : ℚ) = (2 : ℚ) ^ (S n x) - (3 : ℚ) ^ n := by
    rw [Nat.cast_sub hle]; push_cast; ring
  -- Transport the Diophantine identity to ℚ.
  have hsum_eq : (sum_T n x : ℚ) = ((2 : ℚ) ^ (S n x) - (3 : ℚ) ^ n) * (x : ℚ) := by
    have h := congrArg (fun t : ℕ => (t : ℚ)) h_dioph
    simp only [Nat.cast_mul] at h
    rw [hcast] at h
    linarith [h]
  -- D > 0 over ℚ.
  have hD_pos : 0 < (2 : ℚ) ^ (S n x) - (3 : ℚ) ^ n := by
    have h3lt : (3 : ℚ) ^ n < (2 : ℚ) ^ (S n x) := by exact_mod_cast h_thr
    linarith
  have hx_ge : (1 : ℚ) ≤ (x : ℚ) := by exact_mod_cast hx1
  -- N = D·x with x ≥ 1 gives N ≥ D, contradicting N < D.
  nlinarith [h1D, hsum_eq, hD_pos, hx_ge,
    mul_nonneg (le_of_lt hD_pos) (by linarith : (0 : ℚ) ≤ (x : ℚ) - 1)]

end Theorem1_Pure_Positive_Branch

#check theorem_1_pure_positive_branch_closed
#print axioms theorem_1_pure_positive_branch_closed
/--
Unconditional `is_cycle`-facing closure of the pure positive branch.

A profile satisfying `is_pure_positive n x` cannot be a cycle.
-/
theorem theorem_1_pure_positive_branch_no_cycle
    (n x : ℕ) (hn : 0 < n)
    (h_pos : is_pure_positive n x) :
    ¬ is_cycle n x := by
  intro h_cycle
  exact theorem_1_pure_positive_branch_closed n x h_cycle hn h_pos

section Theorem1_Pure_Negative_Branch

/--
Concrete closure of the pure negative *no-lift* branch (Lemma 1I / Corollary 1I-1).

If a length-`n ≥ 5` cycle's exponent profile lands in one of the four terminal
configurations enumerated in Lemma 1I (packaged as
`corollary_1I_1_pure_negative_branch`), then the seed `x` — which plays the role
of the cycle ratio `Z` — must satisfy the corresponding integral ratio equation
`Z · D = N`.  Lemma 1I (`lemma_1I_case_*_no_integer_ratio`) refutes each such
equation, so no cycle can occur.

This connects the abstract Lemma 1I candidate-ratio refutations to a genuine
cycle via the Diophantine identity `cycle_diophantine_int` and the per-case
numerator/exponent evaluations (`lemma_1I_case_*_sum_eval`,
`lemma_1I_case_*_S_eval`).
-/
theorem theorem_1_pure_negative_no_lift_branch_closed
    (n x : ℕ) (h_cycle : is_cycle n x) (hn : 5 ≤ n)
    (h_branch : corollary_1I_1_pure_negative_branch n x) : False := by
  have hdioph := cycle_diophantine_int n x h_cycle (by omega)
  rcases h_branch with hI | hII | hIIIA | hIIIB
  · -- Case I: a₁ = 1, a_{n-1} = 2, aₙ = 2;  D = 2^(2n-1) - 3^n.
    have hS := lemma_1I_case_I_S_eval n x hn hI
    have hN := lemma_1I_case_I_sum_eval n x hn hI
    refine lemma_1I_case_I_no_integer_ratio n x (by omega) ?_
    unfold lemma_1I_case_I_ratio_integral_candidate lemma_1I_case_I_D
    rw [hN, hS] at hdioph
    rw [hdioph]; ring
  · -- Case II: a₁ = 1, a_{n-1} = 1, aₙ = 2;  D = 4^(n-1) - 3^n.
    have hS := lemma_1I_case_II_S_eval n x hn hII
    have hN := lemma_1I_case_II_sum_eval n x hn hII
    refine lemma_1I_case_II_no_integer_ratio n x (by omega) ?_
    unfold lemma_1I_case_II_ratio_integral_candidate lemma_1I_case_II_D
    have h4 : (4 : ℤ) ^ (n - 1) = (2 : ℤ) ^ (2 * n - 2) := by
      rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_mul]; congr 1; omega
    rw [hN, hS] at hdioph
    rw [hdioph, h4]; ring
  · -- Case III-A: a₁ = 1, a_{n-1} = 2, aₙ = 1;  D = 2^(2n-2) - 3^n.
    have hS := lemma_1I_case_IIIA_S_eval n x hn hIIIA
    have hN := lemma_1I_case_IIIA_sum_eval n x hn hIIIA
    refine lemma_1I_case_IIIA_no_integer_ratio n x (by omega) ?_
    unfold lemma_1I_case_IIIA_ratio_integral_candidate lemma_1I_case_IIIA_D
    rw [hN, hS] at hdioph
    rw [hdioph]; ring
  · -- Case III-B: a₁ = 1, a_{n-1} = 1, aₙ = 1;  D = 2^(2n-3) - 3^n.
    have hS := lemma_1I_case_IIIB_S_eval n x hn hIIIB
    have hN := lemma_1I_case_IIIB_sum_eval n x hn hIIIB
    refine lemma_1I_case_IIIB_no_integer_ratio n x (by omega) ?_
    unfold lemma_1I_case_IIIB_ratio_integral_candidate lemma_1I_case_IIIB_D
    rw [hN, hS] at hdioph
    rw [hdioph]; ring
#check theorem_1_pure_negative_no_lift_branch_closed
#print axioms theorem_1_pure_negative_no_lift_branch_closed

/--
`is_cycle`-facing form of the pure negative no-lift branch closure.
-/
theorem theorem_1_pure_negative_no_lift_branch_no_cycle
    (n x : ℕ) (hn : 5 ≤ n)
    (h_branch : corollary_1I_1_pure_negative_branch n x) :
    ¬ is_cycle n x := by
  intro h_cycle
  exact theorem_1_pure_negative_no_lift_branch_closed n x h_cycle hn h_branch

end Theorem1_Pure_Negative_Branch

#check theorem_1_pure_negative_no_lift_branch_no_cycle
#print axioms theorem_1_pure_negative_no_lift_branch_no_cycle

section Theorem1_Pure_Negative_Branch_AllN

/--
Pure negative no-lift branch, length `n = 1`.

The no-lift core forces `val (T^[0] x) = val x = 1`.  For `n = 1` the two terminal
constraints (`a_{n-1}`, `a_n`) both collapse onto index `0`, so Cases I, II, III-A
directly contradict `val x = 1`.  In Case III-B the profile is consistent
(`val x = 1`), but then `S 1 x = 1` and the cycle existence threshold
`3^1 < 2^(S 1 x)` reads `3 < 2`, a contradiction.
-/
lemma pure_negative_branch_n_eq_one
    (x : ℕ) (h_cycle : is_cycle 1 x)
    (h_branch : corollary_1I_1_pure_negative_branch 1 x) : False := by
  have hthr := cycle_existence_threshold 1 x h_cycle (by decide)
  rcases h_branch with hI | hII | hIIIA | hIIIB
  · obtain ⟨⟨hc, _⟩, ht1, _⟩ := hI; simp_all
  · obtain ⟨⟨hc, _⟩, _, ht2⟩ := hII; simp_all
  · obtain ⟨⟨hc, _⟩, ht1, _⟩ := hIIIA; simp_all
  · obtain ⟨⟨hc, _⟩, _, _⟩ := hIIIB; simp_all +decide [S]

/--
Pure negative no-lift branch, length `n = 2`.

Core forces `val x = 1`; the `n-2 = 0` terminal constraint again lands on index `0`,
so Cases I and III-A contradict `val x = 1`.  In Cases II and III-B the profile is
consistent but `S 2 x ∈ {3, 2}`, and the threshold `3^2 = 9 < 2^(S 2 x) ≤ 8` fails.
-/
lemma pure_negative_branch_n_eq_two
    (x : ℕ) (h_cycle : is_cycle 2 x)
    (h_branch : corollary_1I_1_pure_negative_branch 2 x) : False := by
  have hthr := cycle_existence_threshold 2 x h_cycle (by decide)
  rcases h_branch with hI | hII | hIIIA | hIIIB
  · obtain ⟨⟨hc, _⟩, ht1, _⟩ := hI; simp_all
  · obtain ⟨⟨hc, _⟩, _, ht2⟩ := hII; simp_all +decide [S]
  · obtain ⟨⟨hc, _⟩, ht1, _⟩ := hIIIA; simp_all
  · obtain ⟨⟨hc, _⟩, _, ht2⟩ := hIIIB; simp_all +decide [S]

/--
Pure negative no-lift branch, length `n = 3`.

Here the terminal indices `n-2 = 1`, `n-1 = 2` are disjoint from `0`, so `val x = 1`
is consistent.  Cases II, III-A, III-B give `S 3 x ∈ {4,4,3}` with `3^3 = 27 ≥ 2^(S 3 x)`,
failing the threshold.  Case I gives the profile `(1,2,2)`, `S 3 x = 5`,
`sum_T 3 x = 23`; the cycle Diophantine identity yields `23 = (2^5 - 3^3)·x = 5·x`,
impossible for `x : ℕ`.
-/
lemma pure_negative_branch_n_eq_three
    (x : ℕ) (h_cycle : is_cycle 3 x)
    (h_branch : corollary_1I_1_pure_negative_branch 3 x) : False := by
  rcases h_branch with hI | hII | hIIIA | hIIIB
  · obtain ⟨⟨hc, _⟩, ht1, ht2⟩ := hI
    have h1 : val ((T^[1]) x) = 2 := ht1
    have h2 : val ((T^[2]) x) = 2 := ht2
    have hd := cycle_diophantine_int 3 x h_cycle (by decide)
    simp only [sum_T, Finset.sum_range_succ, Finset.sum_range_zero, S,
      hc, h1, h2] at hd
    norm_num at hd
    omega
  · obtain ⟨⟨hc, _⟩, ht1, ht2⟩ := hII
    have hthr := cycle_existence_threshold 3 x h_cycle (by decide)
    simp_all +decide [S]
  · obtain ⟨⟨hc, _⟩, ht1, ht2⟩ := hIIIA
    have hthr := cycle_existence_threshold 3 x h_cycle (by decide)
    simp_all +decide [S]
  · obtain ⟨⟨hc, _⟩, ht1, ht2⟩ := hIIIB
    have hthr := cycle_existence_threshold 3 x h_cycle (by decide)
    simp_all +decide [S]

/--
Pure negative no-lift branch, length `n = 4`.

Cases II, III-A, III-B give `S 4 x ∈ {6,6,5}` with `3^4 = 81 ≥ 2^(S 4 x)`, failing the
threshold.  Case I gives the profile `(1,2,2,2)`, `S 4 x = 7`, `sum_T 4 x = 101`; the
cycle Diophantine identity yields `101 = (2^7 - 3^4)·x = 47·x`, impossible for `x : ℕ`.
-/
lemma pure_negative_branch_n_eq_four
    (x : ℕ) (h_cycle : is_cycle 4 x)
    (h_branch : corollary_1I_1_pure_negative_branch 4 x) : False := by
  rcases h_branch with hI | hII | hIIIA | hIIIB
  · obtain ⟨⟨hc, hIco⟩, ht1, ht2⟩ := hI
    have hv1 : val ((T^[1]) x) = 2 := hIco 1 (by decide)
    have h2 : val ((T^[2]) x) = 2 := ht1
    have h3 : val ((T^[3]) x) = 2 := ht2
    have hd := cycle_diophantine_int 4 x h_cycle (by decide)
    simp only [sum_T, Finset.sum_range_succ, Finset.sum_range_zero, S,
      hc, hv1, h2, h3] at hd
    norm_num at hd
    omega
  · obtain ⟨⟨hc, hIco⟩, ht1, ht2⟩ := hII
    have hv1 : val ((T^[1]) x) = 2 := hIco 1 (by decide)
    have hthr := cycle_existence_threshold 4 x h_cycle (by decide)
    simp_all +decide [S]
  · obtain ⟨⟨hc, hIco⟩, ht1, ht2⟩ := hIIIA
    have hv1 : val ((T^[1]) x) = 2 := hIco 1 (by decide)
    have hthr := cycle_existence_threshold 4 x h_cycle (by decide)
    simp_all +decide [S]
  · obtain ⟨⟨hc, hIco⟩, ht1, ht2⟩ := hIIIB
    have hv1 : val ((T^[1]) x) = 2 := hIco 1 (by decide)
    have hthr := cycle_existence_threshold 4 x h_cycle (by decide)
    simp_all +decide [S]

/--
Unconditional closure of the pure negative no-lift branch for **all** cycle lengths
`n ≥ 1`.

For `n ≥ 5` this is the previously established
`theorem_1_pure_negative_no_lift_branch_closed` (Mechanism 2 route through Lemma 1I).
For `1 ≤ n < 5` the branch's exponent profile directly contradicts the cycle
condition — either through an inconsistent 2-adic valuation at the seed, the cycle
existence threshold `3^n < 2^(S n x)`, or non-integrality of the forced cycle ratio.
-/
theorem theorem_1_pure_negative_branch_all_closed
    (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n)
    (h_branch : corollary_1I_1_pure_negative_branch n x) : False := by
  by_cases h5 : 5 ≤ n
  · exact theorem_1_pure_negative_no_lift_branch_closed n x h_cycle h5 h_branch
  · have h5' : n < 5 := by omega
    interval_cases n
    · exact pure_negative_branch_n_eq_one x h_cycle h_branch
    · exact pure_negative_branch_n_eq_two x h_cycle h_branch
    · exact pure_negative_branch_n_eq_three x h_cycle h_branch
    · exact pure_negative_branch_n_eq_four x h_cycle h_branch

/--
`is_cycle`-facing form of the all-`n` pure negative no-lift branch closure.
-/
theorem theorem_1_pure_negative_branch_all_no_cycle
    (n x : ℕ) (hn : 0 < n)
    (h_branch : corollary_1I_1_pure_negative_branch n x) :
    ¬ is_cycle n x := by
  intro h_cycle
  exact theorem_1_pure_negative_branch_all_closed n x h_cycle hn h_branch

end Theorem1_Pure_Negative_Branch_AllN
#check theorem_1_pure_negative_branch_all_closed
#print axioms theorem_1_pure_negative_branch_all_closed

section Theorem1_Mixed_Branch

/-
Lemma 1K, ratio ceiling is preserved under positive exponent inflation.

If a base exponent profile `a` has a positive denominator `D(a) > 0` and a
sub-`5` ratio, expressed in cleared-denominator form as `N(a) < 5 · D(a)`, then
every componentwise positive inflation `ahat` also satisfies `N(ahat) < 5 · D(ahat)`,
i.e. its ratio stays strictly below `5`.

This is the quantitative "1K keeps the ratio `< 5`" step used by the mixed
branch: it turns the minimal lifted-tail representative's bound `Z < 5` into the
same bound for the maximal lift and for any further positive perturbation.
-/
lemma lemma_1K_ratio_stays_below_five
    (n : ℕ) (a ahat : ℕ → ℕ)
    (h_inf : lemma_1K_componentwise_positive_inflation n a ahat)
    (hD_pos : 0 < lemma_1K_D n a)
    (h_base : lemma_1K_N n a < 5 * lemma_1K_D n a) :
    lemma_1K_N n ahat < 5 * lemma_1K_D n ahat := by
  have hprod := lemma_1K_positive_inflation_decreases_ratio n a ahat h_inf hD_pos
  have hgrow := lemma_1K_denominator_strict_growth n a ahat h_inf hD_pos
  have hpow := pow_pos (by norm_num : (0 : ℤ) < 2) (lemma_1K_R n a ahat)
  nlinarith [mul_pos hpow hD_pos]

/--
Mixed-branch mechanism route (Lemma 1H signature for the mixed branch).

After the Lemma 1F terminal boundary obstruction is removed, a mixed
perturbation cycle candidate must enter one of the permissible 3-adic
trajectories of Lemma 1H.  For a numerator-dominant integer cycle the surviving
possibilities are exactly:

* the `p = 1` no-lift endpoint of Mechanism 2, whose terminal configurations are
  the four cases of Corollary 1I-1 (`corollary_1I_1_pure_negative_branch`);
* the genuine `p ≥ 2` lifted branch realized by the *minimal* lifted-tail
  representative, handled by Lemma 1J (`lemma_1J_minimal_lift_representative`); or
* any *further positive perturbation* of a below-`5` base representative — the
  maximal lift, replacing permitted `1`'s by odd positive exponents, or inflating
  the lifted-tail / terminal exponents — recorded here as a componentwise positive
  inflation `ahat` of a base profile `a` whose cleared-denominator ratio is `< 5`,
  together with the cycle Diophantine identity `N(ahat) = D(ahat) · x`.
-/
def theorem_1_mixed_branch_route (n x : ℕ) : Prop :=
  corollary_1I_1_pure_negative_branch n x ∨
    (∃ floor, lemma_1J_minimal_lift_representative n x floor) ∨
      (∃ a ahat : ℕ → ℕ,
        lemma_1K_componentwise_positive_inflation n a ahat ∧
          0 < lemma_1K_D n a ∧
            lemma_1K_N n a < 5 * lemma_1K_D n a ∧
              lemma_1K_N n ahat = lemma_1K_D n ahat * (x : ℤ))

/--
Closure of the mixed branch of Theorem 1.

A nontrivial positive integer cycle whose perturbation profile routes through the
Lemma 1H mixed-branch mechanism signature `theorem_1_mixed_branch_route` cannot
exist.  The three cases are discharged, respectively, by the pure-negative
no-lift closure (Corollary 1I-1 / Lemma 1I), by Lemma 1J for the minimal lifted
representative, and by Lemma 1K for the maximal lift / any further positive
perturbation (which keeps the ratio `< 5`, contradicting the numerator-dominant
requirement `Z ≥ 5` supplied by Constraint 3).
-/
theorem theorem_1_mixed_branch_closed
    (n x : ℕ) (h_cycle : is_cycle n x) (hn : 0 < n) (hx : x > 1)
    (h_route : theorem_1_mixed_branch_route n x) : False := by
  rcases h_route with hI | ⟨floor, hrep⟩ | ⟨a, ahat, h_inf, hD_pos, h_base, h_dioph⟩
  · -- `p = 1` no-lift endpoint of Mechanism 2: Corollary 1I-1 / Lemma 1I.
    exact theorem_1_pure_negative_branch_all_closed n x h_cycle hn hI
  · -- Minimal lifted-tail representative: Lemma 1J gives `Z < 5`.
    exact lemma_1J_minimal_lift_representative_cycle_closed n x floor h_cycle hn hx hrep
  · -- Maximal lift / further positive perturbation: Lemma 1K keeps `Z < 5`.
    have h5 : lemma_1K_N n ahat < 5 * lemma_1K_D n ahat :=
      lemma_1K_ratio_stays_below_five n a ahat h_inf hD_pos h_base
    have hgrow : (2 : ℤ) ^ lemma_1K_R n a ahat * lemma_1K_D n a < lemma_1K_D n ahat :=
      lemma_1K_denominator_strict_growth n a ahat h_inf hD_pos
    have hpow : (0 : ℤ) < (2 : ℤ) ^ lemma_1K_R n a ahat := by positivity
    have hDhat_pos : 0 < lemma_1K_D n ahat := by nlinarith [mul_pos hpow hD_pos]
    have hxZ : (x : ℤ) < 5 := by nlinarith [h_dioph, h5, hDhat_pos]
    have hxlt : x < 5 := by exact_mod_cast hxZ
    have hge : 5 ≤ x := constraint_3_nontrivial_cycle_ratio_ge_five n x h_cycle hn hx
    omega
#check theorem_1_mixed_branch_closed
#print axioms theorem_1_mixed_branch_closed

/--
`is_cycle`-facing form of the mixed branch closure.

A nontrivial profile routing through the Lemma 1H mixed-branch mechanism
signature cannot be a cycle.
-/
theorem theorem_1_mixed_branch_no_cycle
    (n x : ℕ) (hn : 0 < n) (hx : x > 1)
    (h_route : theorem_1_mixed_branch_route n x) :
    ¬ is_cycle n x := by
  intro h_cycle
  exact theorem_1_mixed_branch_closed n x h_cycle hn hx h_route

end Theorem1_Mixed_Branch
#check theorem_1_mixed_branch_no_cycle
#print axioms theorem_1_mixed_branch_no_cycle

/--
Cycle-facing 1H route.

Projects the permissible-mechanism
part out of `lemma_1H_cycle_forces_signature`, whose proof already runs through
the 2D -> 1F -> 1H chain.
-/
lemma nontrivial_cycle_forces_1H_permissible_route
    (n x : ℕ)
    (h_cycle : is_cycle n x)
    (hn : 1 < n)
    (hx : x > 1) :
    lemma_1H_permissible_trajectory n x (cycle_seed_target n x) := by
  exact (lemma_1H_cycle_forces_signature n x h_cycle hn hx).2.2

#check nontrivial_cycle_forces_1H_permissible_route
#print axioms nontrivial_cycle_forces_1H_permissible_route

/--
Cycle-facing 1H mechanism split.

This is just the unfolded callable form of the permissible 1H route.
-/
lemma nontrivial_cycle_forces_1H_mechanism_split
    (n x : ℕ)
    (h_cycle : is_cycle n x)
    (hn : 1 < n)
    (hx : x > 1) :
    mechanism_1_direct_lift n x (cycle_seed_target n x) ∨
      mechanism_2_hybrid_cancellation_lift n x (cycle_seed_target n x) := by
  exact nontrivial_cycle_forces_1H_permissible_route n x h_cycle hn hx

theorem nontrivial_cycle_forces_1H_branch_alternative
    (n x : ℕ)
    (h_cycle : is_cycle n x)
    (hn : 1 < n)
    (hx : x > 1) :
    mechanism_1_direct_lift n x (cycle_seed_target n x) ∨
      mechanism_2_hybrid_cancellation_lift n x (cycle_seed_target n x) := by
  have h1H :
      mechanism_1_direct_lift n x (cycle_seed_target n x) ∨
        mechanism_2_hybrid_cancellation_lift n x (cycle_seed_target n x) :=
    nontrivial_cycle_forces_1H_mechanism_split n x h_cycle hn hx

  exact h1H
