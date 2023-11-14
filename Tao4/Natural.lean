import Std.Tactic.RCases
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LibrarySearch

inductive mynat
| zero : mynat -- Axiom 2.1
| succ (n : mynat) : mynat -- Axiom 2.2

namespace mynat

-- Axiom 2.1
instance : OfNat mynat 0 where ofNat := mynat.zero
@[simp]
theorem zero_eq_zero : mynat.zero = 0 := rfl

-- Definition 2.1.3
def one : mynat := succ 0
instance : OfNat mynat 1 where ofNat := one
theorem one_eq_succ_zero : 1 = succ 0 := by rfl

-- Axiom 2.3
theorem zero_ne_succ (m : mynat) : succ m ≠ (0 : mynat) := by intro h ; cases h


theorem succ_ne_zero (m : mynat) :  succ m ≠ (0 : mynat) := by intro h ; cases h.symm

-- Axiom 2.4
theorem succ_inj (m n : mynat) : succ n = succ m → n = m := by
  intro h
  cases h
  rfl

theorem succ_of_eq {a b : mynat} (h : a = b) : succ a = succ b := by
  rw [h]

theorem succ_of_neq {a b : mynat} (h : a ≠ b) : succ a ≠ succ b := by
  intro h1
  have h2 := succ_inj _ _ h1
  contradiction

theorem neq_succ_inj (m n : mynat) (h : succ n ≠ succ m) : n ≠ m :=  by
  intro h1
  rw [h1] at h
  exact h rfl


-- Proposition 2.1.11
theorem induct (P : mynat -> Prop) (base : P mynat.zero) (ind : ∀a, P a → P (succ a)) : ∀ a, P a := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact (ind n) ih


-- ≠ is symmetric
example (a b : mynat) (h : a ≠ b) : b ≠ a := by
  exact h.symm

-- 2.2

-- Definition 2.2.1
def add : mynat → mynat → mynat
| 0, n => n
| (succ n), m => succ (add n m)

-- instance
instance : Add mynat where
  add := add

-- Proposition 2.1.6 (can only be done with numerals after defining addition

def recurse (x : Nat) : mynat :=
  if x = (0 : Nat) then
    mynat.zero
  else
    succ (recurse (x-(1 : Nat)))

instance : OfNat mynat n where ofNat := recurse n

example : (4 : mynat) ≠ (0 : mynat) := by
  have h1 : 4 = succ 3 := by rfl
  rw [h1]
  exact succ_ne_zero _

@[simp]
theorem succ_add (n m : mynat) : succ n + m = succ (n+m) := rfl
@[simp]
theorem zero_add (n : mynat) : 0 + n = n := rfl

-- Lemma 2.2.2
@[simp]
theorem add_zero (n : mynat) : n + (0 : mynat) = n := by
  induction n with
  | zero => rw [zero_eq_zero] ; rw[zero_add]
  | succ n hyp => rw [succ_add] ; rw[hyp]

-- Lemma 2.2.3
@[simp]
theorem add_succ (n m : mynat) : n + succ m = succ (n+m) := by
  induction n with
  | zero =>
    rw [zero_eq_zero]
    rw [zero_add]
    rw [zero_add]
  | succ n hyp =>
    rw [succ_add]
    rw [hyp]
    rw [succ_add]

-- Proposition 2.2.4
theorem add_comm (a b : mynat) : a+b = b+a := by
  induction b with
  | zero =>
  rw [zero_eq_zero]
  rw [zero_add]
  rw [add_zero]
  | succ n hyp =>
  rw [add_succ]
  rw [succ_add]
  rw [hyp]

-- Proposition 2.2.5
theorem add_assoc (a b c : mynat) : a+(b+c) = (a+b)+c := by
  induction c with
  | zero =>
  rw [zero_eq_zero]
  rw [add_zero]
  rw [add_zero]
  | succ n hyp =>
  rw [add_succ]
  rw [add_succ]
  rw [hyp]
  rw [add_succ]

-- Proposition 2.2.6
@[simp]
theorem add_cancel {a b c : mynat} (h1 : a+b = a+c) : b = c := by
  induction a with
  | zero =>
  rw [zero_eq_zero] at h1
  rw [zero_add] at h1
  rw [zero_add] at h1
  exact h1
  | succ a hyp =>
  rw [succ_add] at h1
  rw [succ_add] at h1
  apply hyp
  apply succ_inj
  exact h1

-- Propositinn 2.2.8
theorem pos_iff_pos (a b : mynat) : a ≠ 0 → a+b ≠ 0 := by
  intro h1
  intro h
  induction a with
  | zero =>
  rw [zero_eq_zero] at h1
  exact h1 rfl
  | succ n _ =>
  rw [succ_add] at h
  exact succ_ne_zero _ h

example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h
  . apply Or.inr
    assumption
  . apply Or.inl
    assumption

-- Corollary 2.2.9
theorem zero_iff_eq_zero (a b : mynat) : a+b = 0 → a = 0 ∧ b = 0 := by
  intro h1
  constructor
  · cases a with
    | zero => rw [zero_eq_zero]
    | succ a => have h2 := succ_ne_zero (a+b) ; rw [succ_add] at h1 ; contradiction
  · cases b with
    | zero => rw [zero_eq_zero]
    | succ b => have h2 := succ_ne_zero (a+b) ; rw [add_succ] at h1 ; contradiction

-- Lemma 2.2.10
theorem only_one (a b c : mynat) : succ b = a ∧ succ c = a → b = c := by
  intro h
  cases h with
  | intro h_left h_right =>
  rw [h_right.symm] at h_left
  apply succ_inj
  exact h_left

def le (a b : mynat) : Prop :=  ∃ (c : mynat), b = a + c
def lt (a b : mynat) : Prop :=  ∃ (c : mynat), b = a + c ∧ a ≠ b

instance : LE mynat where le := le
instance : LT mynat where lt := lt

theorem le_eq (a b : mynat) : le a b = (a ≤ b) := by rfl
theorem lt_eq (a b : mynat) : lt a b = (a < b) := by rfl

theorem lt_def (a b : mynat) : a < b ↔ ∃ (c : mynat), b = a + c ∧ a ≠ b := by {
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
  · intro h
    rcases h with ⟨c, h⟩
    use c
}

theorem le_def (a b : mynat) : a ≤ b ↔ ∃ (c : mynat), b = a + c := by {
  constructor
  · intro h
    rcases h with ⟨c, h⟩
    use c
  · intro h
    rcases h with ⟨c, h⟩
    use c
}

theorem lt_neq_zero (a b : mynat) : a < b ↔ ∃ (c : mynat), b = a + c ∧ c ≠ 0 := by {
  constructor
  · intro h1
    rw [lt_def] at h1
    rcases h1 with ⟨c, h1, h2⟩
    use c
    constructor
    · exact h1
    · intro h3
      rw [h3, add_zero] at h1
      exact h2 h1.symm
  · intro h1
    rcases h1 with ⟨c, h1, h2⟩
    use c
    constructor
    exact h1
    intro h3
    rw [h3] at h1
    nth_rw 1 [←add_zero b] at h1
    have h4 := add_cancel h1
    exact h2 h4.symm
}

example : ∃ x : mynat, x > 0 := by
  apply Exists.intro 1
  apply Exists.intro 1
  constructor
  rw [zero_add]
  rw [one_eq_succ_zero]
  exact (succ_ne_zero 0).symm

@[simp]
theorem reflexivity (a : mynat) : a ≥ a := by
  apply Exists.intro 0
  rw [add_zero]

theorem transitivity (a b c : mynat) (hab : a ≥ b) (hbc : b ≥ c) : a ≥ c  := by
  cases hab with
  | intro hab_w hab_h =>
  cases hbc with
  | intro hbc_w hbc_h =>
  rw [hbc_h] at hab_h
  apply Exists.intro (hbc_w + hab_w)
  rw [add_assoc]
  exact hab_h

theorem antisymmetry (a b : mynat) (hab : a ≥ b) (hba : b ≥ a) : a = b  := by
  cases hab with
  | intro hab_w hab_h =>
  cases hba with
  | intro hba_w hba_h =>
  rw [hba_h, ←add_assoc] at hab_h
  nth_rw 1 [(add_zero a).symm] at hab_h
  have h1 := (add_cancel hab_h).symm
  have h2 := (zero_iff_eq_zero _ _ h1).left
  rw [h2] at hba_h
  rw [add_zero] at hba_h
  exact hba_h.symm

theorem prop_d (a b c : mynat) (hab : a ≥ b) : a+c ≥ b+c := by
  cases hab with
  | intro hab_w hab_h =>
  rw [hab_h]
  apply Exists.intro hab_w
  rw [←add_assoc]
  rw [add_comm hab_w c]
  rw [add_assoc]


theorem prop_f (a b c : mynat) (hab : a ≥ b) : a+c ≥ b+c := by
  cases hab with
  | intro hab_w hab_h =>
  rw [hab_h]
  apply Exists.intro hab_w
  rw [←add_assoc]
  rw [add_comm hab_w c]
  rw [add_assoc]

theorem prop_e (a b : mynat) (hab : a < b) : succ a ≤ b := by
  match hab with
  | ⟨d, ⟨h1, h2⟩⟩ =>
  cases d with
  | zero => rw [zero_eq_zero, add_zero] at h1; have contra := h1.symm; contradiction
  | succ c =>
  rw [add_succ, ←succ_add] at h1
  apply Exists.intro c
  exact h1

-- theorem neq_succ_inj {m n : mynat} (h : succ n ≠ succ m) : n ≠ m

theorem neq_succ (a : mynat) : a ≠ succ a := by
  induction a with
  | zero =>
  rw [zero_eq_zero]
  exact (succ_ne_zero 0).symm
  | succ a hyp =>
  exact succ_of_neq hyp

theorem leq_eq_or (a b : mynat) (h1 : a ≤ b) : a = b ∨ a < b := by
  match h1 with
  | ⟨w, h2⟩ =>
  cases w with
  | zero =>
    rw [zero_eq_zero, add_zero] at h2
    apply Or.inl
    exact h2.symm
  | succ n =>
    apply Or.inr
    apply Exists.intro (succ n)
    constructor
    exact h2
    intro h3
    rw [h3] at h2
    nth_rw 1 [←add_zero b] at h2
    have h4 := add_cancel h2
    contradiction

theorem trichotomy (a b : mynat) : a < b ∨ a = b ∨ a > b := by
  induction a with
  | zero =>
    rw [zero_eq_zero]
    cases b with
    | zero =>
      rw [zero_eq_zero]
      apply Or.inr
      apply Or.inl
      rfl
    | succ n =>
      apply Or.inl
      apply Exists.intro (succ n)
      constructor
      rw [zero_add]
      exact (succ_ne_zero n).symm
  | succ a hyp =>
    cases hyp with
    | inl h1 =>
      -- a < b
      have h2 := prop_e a b h1
      have h3 : succ a = b ∨ succ a < b := leq_eq_or (succ a) b h2
      cases h3 with
      | inl h =>
        apply Or.inr
        apply Or.inl
        exact h
      | inr h =>
        apply Or.inl
        exact h
    | inr h1 =>
      cases h1 with
      | inl h =>
        -- a = b
        apply Or.inr
        apply Or.inr
        rw [h]
        apply Exists.intro 1
        constructor
        rw [one_eq_succ_zero, add_succ, add_zero]
        exact neq_succ b
      | inr h =>
        -- a > b
        apply Or.inr
        apply Or.inr
        match h with
        | ⟨w, ⟨h1, h2⟩⟩ =>
        apply Exists.intro (succ w)
        constructor
        rw [add_succ, h1]
        intro h3
        rw [h3, succ_add, ←add_succ] at h1
        nth_rw 1 [←add_zero a] at h1
        have h4 := add_cancel h1
        contradiction

def mul : mynat → mynat → mynat
| 0, _ => 0
| (succ n), m => (mul n m) + m

instance : Mul mynat where
  mul := mul

@[simp]
theorem zero_mul (n : mynat) : 0*n = 0 := by rfl
@[simp]
theorem succ_mul (n m : mynat) : succ n * m = n*m + m := by rfl

@[simp]
theorem mul_zero (n : mynat) : n*0 = 0 := by {
  induction n with
  | zero => rw [zero_eq_zero, zero_mul 0]
  | succ n hn => {
    rw [succ_mul, hn, add_zero 0]
  }
}

@[simp]
theorem mul_succ (n m : mynat) : m * n + m = m * succ n := by {
  induction m with
  | zero => rw [zero_eq_zero, zero_mul, zero_mul, add_zero]
  | succ m hm => {
    -- learn how to use simp to make stuff like this trivial
    rw [succ_mul, succ_mul, ←hm, ←add_assoc (m*n) (n) (succ m), add_succ n m, ←add_assoc (m*n) (m) (succ n), add_succ m n, add_comm m n]
  }
}

theorem mul_comm (n m : mynat) : n*m = m*n := by {
  induction n with
  | zero => rw [zero_eq_zero, zero_mul, mul_zero]
  | succ n hn => rw [succ_mul, hn, ←mul_succ]
}
theorem no_zero_divisors (n m : mynat) : n*m = 0 → n = 0 ∨ m = 0 := by {
  intro h1
  cases n with
  | zero => simp
  | succ n => {
    simp at h1
    cases m with
    | zero => simp
    | succ m => simp at h1
  }
}

theorem left_distrib (a b c : mynat) : a*(b+c) = a*b+a*c := by {
  induction a with
  | zero => rw [zero_eq_zero, zero_mul, zero_mul, zero_mul, add_zero]
  | succ a ha => {
    simp
    rw [ha, add_assoc, add_comm (a*c) c, add_assoc, ←add_assoc, add_comm, ←(add_assoc (a*b)), add_comm (a*b) (b+c), add_assoc] -- AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
  }
}

theorem mul_assoc (a b c : mynat) : (a*b)*c = a*(b*c) := by {
    induction a with
  | zero => simp
  | succ a ha => {
    rw [succ_mul, succ_mul, ←ha, mul_comm, left_distrib, ←mul_comm, mul_comm b c]
  }
}

-- theorem add_cancel (a b c : mynat) (h1 : a+b = a+c) : b = c := by

theorem pos_mul_pos_ne_zero {a b : mynat} (a_pos : a > 0) (b_pos : b > 0) : a*b ≠ 0 := by {
  intro h1
  cases a with
  | zero => {
    simp at *
    have h2 := (lt_neq_zero _ _).mp a_pos
    rcases h2 with ⟨d,h2,h3⟩
    rw [zero_add] at h2
    exact h3 h2.symm
  }
  | succ a => {
    rw [mul_comm, ←mul_succ] at h1

    have h2 := (lt_neq_zero _ _).mp b_pos
    rcases h2 with ⟨c,h2,h3⟩
    rw [zero_add] at h2
    rw [←h2] at h3
    cases b with
    | zero => simp at h3
    | succ b => {
      rw [add_comm, succ_add] at h1
      exact (succ_ne_zero _) h1
    }
  }
}

theorem le_mul {a b c : mynat} (a_lt_b: a < b) (c_pos : c > 0) : a*c < b*c := by {
  have h1 := (lt_neq_zero a b).mp a_lt_b
  rcases h1 with ⟨d,h1,h2⟩
  have h3 : b*c = a*c + d*c := by {
    rw [h1, mul_comm, left_distrib, mul_comm, mul_comm c d]
  }

  use d*c
  constructor
  · exact h3
  · intro h4
    rw [h4] at h3
    nth_rw 1 [←add_zero (b*c)] at h3
    have h5 := add_cancel h3
    have d_pos : d > 0 := by {
      use d
      constructor
      rw [zero_add]
      exact h2.symm
    }
    have h6 := pos_mul_pos_ne_zero c_pos d_pos
    rw [mul_comm] at h6
    exact h6 h5.symm
}

theorem mul_cancel {a b c : mynat} (c_pos : c > 0) (h1 : a*c = b*c) : a = b := by {
  have tri := trichotomy a b
  cases tri with
  | inl h2 => {
    have h3 := le_mul h2 c_pos
    rcases h3 with ⟨d,_,h4⟩
    contradiction
  }
  | inr duo => {
      cases duo with
      | inl h2 => exact h2
      | inr h2 => {
        have h3 := le_mul h2 c_pos
        rcases h3 with ⟨d,_,h4⟩
        have h5 := h4.symm
        contradiction
      }
  }
}

theorem mul_cancel_right {a b c : mynat} (c_pos : c > 0) (h1 : c*a = c*b) : a = b := by {
  rw [mul_comm, mul_comm c b] at h1
  exact mul_cancel c_pos h1
}

-- now, consider mynat to be a semiring in mathlib
@[simp]
theorem mul_one (a : mynat) : a*1 = a := by {
  rw [mul_comm, one_eq_succ_zero, succ_mul, zero_mul, zero_add]
}

@[simp]
theorem right_distrib (a b c : mynat) : (a + b) * c = a * c + b * c := by {
  rw [mul_comm, mul_comm a c, mul_comm b c]; exact left_distrib c a b
}
instance : CommSemiring mynat where
  mul_one := mul_one
  add_assoc := by intro a b c; exact (add_assoc a b c).symm
  zero_add := zero_add
  add_zero := add_zero
  add_comm := add_comm
  left_distrib := left_distrib
  right_distrib := right_distrib
  zero_mul := zero_mul
  mul_zero := mul_zero
  mul_assoc := mul_assoc
  one_mul := by intro a; rw [mul_comm, mul_one]
  mul_comm := mul_comm

-- showing that ring now works properly
example (a b : mynat) : a*b = b*a := by {
  ring
}

@[simp]
theorem succ_eq_add (a : mynat) : succ a = a + 1 := by {
  induction a with
  | zero => simp; rfl
  | succ a ha => rw [ha]; nth_rw 2 [←ha]; rw [←succ_add]
}

theorem exists_pos_pred {a : mynat} (h : a ≠ 0) : ∃ n, succ n = a := by {
  cases a with
  | zero => contradiction
  | succ a => use a
}
@[simp]
theorem add_cancel_right {a b c : mynat} (h1 : b+a = c+a) : b = c := by {
  rw [add_comm, add_comm c a] at h1
  exact add_cancel h1
}

theorem add_cancel' {a b c : mynat} : b = c → a+b = a+c := by {
  intro h
  rw [h]
}

theorem add_cancel_right' {a b c : mynat} : b = c → b+a = c+a := by {
  intro h
  rw [h]
}

-- Proposition 2.3.9
theorem euclid_alg (n q : mynat) (q_pos : q > 0) : ∃ (m r: mynat), 0 ≤ r ∧ r < q ∧ n = m*q+r := by {
  induction n with
  | zero => {
    rw [zero_eq_zero]
    use 0,0
    constructor
    simp
    constructor
    rcases q_pos with ⟨a, hq1, hq2⟩
    use a
    constructor
  }
  | succ n hn => {
    rcases hn with ⟨m, r, hn⟩
    have tri := trichotomy (r+1) q
    cases tri with
    | inl h_le => {
      use m, r+1
      constructor
      use r+1
      simp
      constructor
      have hn1 := hn.right.left
      have hn2 := (lt_neq_zero _ _).mp hn1
      rcases hn2 with ⟨g, h1, h2⟩
      have h3 := exists_pos_pred h2
      rcases h3 with ⟨g_pred, h4⟩

      -- r + 1 < q
      use g_pred
      constructor
      rw [succ_eq_add] at h4
      rw [add_comm] at h4
      rw [←add_assoc r 1 g_pred, h4]
      exact h1

      -- here
      intro h3
      rw [h3] at h_le

      rcases h_le with ⟨g', _, hle⟩
      exact hle (by rfl)

      rw [succ_eq_add]
      rw [hn.right.right]
      ring
    }
    | inr duo => {
      cases duo with
      | inl hle => {
        use m+1, 0
        constructor
        simp
        constructor
        have hn1 := hn.right.left
        have hn2 := (lt_neq_zero _ _).mp hn1
        rcases hn2 with ⟨g, _, _⟩
        use q
        constructor
        simp
        rcases q_pos with ⟨_, _, hq⟩
        exact hq

        rw [succ_eq_add]
        ring
        rw [hn.right.right]
        ring
        calc
          1 + m * q + r = m * q + (r + 1) := by ring
          _ = m * q + q := by rw [hle]
      }
      | inr hge => {
        have hn1 := hn.right.left
        rcases hge with ⟨g, h1, h2⟩
        rcases hn1 with ⟨g', h3, h4⟩
        rw [h3, ←add_assoc] at h1
        have h5 := add_cancel h1
        rw [h5] at h2
        cases g with
        | zero => {
          rw [zero_eq_zero] at *
          rw [add_zero] at *
          contradiction
        }
        | succ g => {
          rw [add_succ] at h5
          rw [one_eq_succ_zero] at h5
          rw [succ_eq_add, succ_eq_add] at h5
          have h6 := add_cancel_right h5
          cases g' with
          | zero => {
            rw [zero_eq_zero, add_zero] at h3
            have h3 := h3.symm
            contradiction
          }
          | succ g' => {
            rw [succ_add] at h6
            contradiction
          }
        }
      }
    }
  }
}

def pow : mynat → mynat → mynat
| _, 0 => 1
| n, (succ m) => (pow n m) * n

instance : Pow mynat mynat where
  pow := pow

@[simp]
theorem pow_zero (n : mynat) : n^0 = 1 := by rfl
@[simp]
theorem succ_pow (n m : mynat) : n ^ succ m = n^m * n := by rfl

example (x: mynat) : x ^ 1 = x := by {
  rw [one_eq_succ_zero, succ_pow x 0, pow_zero, one_mul]
}

def beq : mynat → mynat → Bool
  | zero,   zero   => true
  | zero,   succ _ => false
  | succ _, zero   => false
  | succ n, succ m => beq n m

instance : BEq mynat where
  beq := mynat.beq

theorem eq_of_beq_eq_true : {n m : mynat} → Eq (beq n m) true → Eq n m
  | zero,   zero,   _ => rfl
  | zero,   succ _, h => Bool.noConfusion h
  | succ _, zero,   h => Bool.noConfusion h
  | succ n, succ m, h =>
    have : Eq (beq n m) true := h
    have : Eq n m := eq_of_beq_eq_true this
    this ▸ rfl

theorem ne_of_beq_eq_false : {n m : mynat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, _  => Bool.noConfusion h₁
  | zero,   succ _, _,  h₂ => mynat.noConfusion h₂
  | succ _, zero,   _,  h₂ => mynat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have : Eq (beq n m) false := h₁
    mynat.noConfusion h₂ (fun h₂ => absurd h₂ (ne_of_beq_eq_false this))

def decEq (n m : mynat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false => isFalse (ne_of_beq_eq_false h)

@[inline] instance : DecidableEq mynat := mynat.decEq

-- the same as beq but with a different truth table...
def ble : mynat → mynat → Bool
  | zero,   zero   => true
  | zero,   succ _ => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

private theorem clutch_succ {n m : mynat} (h1 : n ≤ m) : succ n ≤ succ m := by {
  rcases h1 with ⟨a, ha⟩
  rw [succ_eq_add, succ_eq_add]
  use a
  rw [← add_assoc, add_comm 1, add_assoc, ha]
}

private theorem clutch_succ' {n m : mynat} (h1 : succ n ≤ succ m) : n ≤ m := by {
  rcases h1 with ⟨a, ha⟩
  rw [succ_eq_add, succ_eq_add, ← add_assoc, add_comm 1, add_assoc] at ha
  use a
  exact add_cancel_right ha
}

theorem leq_of_ble_eq_true : {n m : mynat} → Eq (ble n m) true → n ≤ m
  | zero,   zero,   _ => by use zero; ring
  | zero,   succ n, _ => by use (succ n); rw [zero_eq_zero, zero_add]
  | succ _, zero,   _ => by contradiction
  | succ n, succ m, h =>
    by {
      have h1 : Eq (ble n m) true := h
      have h2 := clutch_succ (leq_of_ble_eq_true h1)
      exact h2
    }

/-
theorem ne_of_beq_eq_false : {n m : mynat} → Eq (beq n m) false → Not (Eq n m)
  | zero,   zero,   h₁, _  => Bool.noConfusion h₁
  | zero,   succ _, _,  h₂ => mynat.noConfusion h₂
  | succ _, zero,   _,  h₂ => mynat.noConfusion h₂
  | succ n, succ m, h₁, h₂ =>
    have : Eq (beq n m) false := h₁
    mynat.noConfusion h₂ (fun h₂ => absurd h₂ (ne_of_beq_eq_false this))
-/
theorem nleq_of_ble_eq_true : {n m : mynat} → Eq (ble n m) false → Not (n ≤ m)
  | zero,   zero,   _ => by contradiction
  | zero,   succ n, _ => by contradiction
  | succ _, zero,   _ => by {
    intro h
    rcases h with ⟨a, ha⟩
    rw [succ_add] at ha
    exact (succ_ne_zero _) ha.symm
  }
  | succ n, succ m, h =>
    by {
      have h1 : Eq (ble n m) false := h
      have h2 := nleq_of_ble_eq_true h1
      intro h3
      have h4 := clutch_succ' h3
      contradiction
    }

def dec_le (n m : mynat) : Decidable (n ≤ m) :=
  match h:ble n m with
  | true  => isTrue (leq_of_ble_eq_true h)
  | false => isFalse (nleq_of_ble_eq_true h)

instance decidableLE : @DecidableRel mynat (· ≤ ·) := by {
  intro a b
  exact dec_le a b
}

end mynat
