import Std.Tactic.RCases
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LibrarySearch
import Tao4.Natural

structure myint where
  mk ::
  l : mynat
  r : mynat

def rel_int (n: myint) (m: myint) : Prop := n.l+m.r = m.l+n.r

theorem rel_int_refl : ∀ x, rel_int x x := by {
  intro x
  constructor
}

theorem rel_int_symm : ∀ {x y}, rel_int x y → rel_int y x := by {
  intro x y h1
  unfold rel_int
  rw [h1]
}

theorem rel_int_trans : ∀ {x y z}, rel_int x y → rel_int y z → rel_int x z := by {
  intros x y z
  intro h_xy
  intro h_yz
  unfold rel_int at *
  apply mynat.add_cancel (a := x.l + y.r)
  nth_rw 1 [h_xy]
  rw [add_comm x.l z.r, ←add_assoc, add_comm (y.l + x.r) z.r, ←add_assoc, add_comm z.r y.l, h_yz]
  ring
}

private theorem is_equivalence_int : Equivalence rel_int where
  refl := rel_int_refl
  symm := rel_int_symm
  trans := rel_int_trans

instance myintSetoid : Setoid (myint) where
  r     := rel_int
  iseqv := is_equivalence_int

def MyInt := Quotient myintSetoid

namespace MyInt

def mk (a b : mynat) : MyInt := Quotient.mk' (myint.mk a b)

-- this is \em
infixl:65 " — "   => mk
infixl:65 " ~ "   => rel_int

theorem rel_nat_int (a b c d: mynat) : a + d = c + b → (a—b) = (c—d) := by {
  intro h
  apply Quot.sound (r := rel_int); unfold rel_int
  exact h
}

theorem rel_int_nat {a b c d: mynat} : (a—b) = (c—d) → a + d = c + b := by {
  intro h
  have h1 := Quotient.exact h
  exact h1
}

private def add_fn (a: myint) (b: myint) : MyInt :=
  mk (a.l+b.l) (a.r+b.r)

private theorem add_respects_nat (a b a' b' c d c' d' : mynat) :
(myint.mk a b) ~ (myint.mk a' b') → (myint.mk c d) ~ (myint.mk c' d') → add_fn (myint.mk a b) (myint.mk c d) = add_fn (myint.mk a' b') (myint.mk c' d') := by {
  intro hab
  intro hcd
  unfold add_fn
  apply rel_nat_int
  ring
  rw [add_comm (a+c) b', ←add_assoc, add_comm b' a, hab]
  rw [add_comm a' c', add_comm (c'+a'+b), ←add_assoc, ←add_assoc, add_comm d c', ←hcd]
  ring
}

private theorem add_respects_1 (a b₁ b₂ : myint) (hb: b₁ ~ b₂) : add_fn a b₁ = add_fn a b₂ := by {
  have ha : a ~ a := by exact rel_int_refl a
  exact (add_respects_nat a.l a.r a.l a.r b₁.l b₁.r b₂.l b₂.r) ha hb
}

private theorem add_respects_2 (a₁ a₂ b : myint) (ha: a₁ ~ a₂) : add_fn a₁ b = add_fn a₂ b := by {
  have hb : b ~ b := by exact rel_int_refl b
  exact (add_respects_nat a₁.l a₁.r a₂.l a₂.r b.l b.r b.l b.r) ha hb
}

def add (a : MyInt) (b : MyInt) : MyInt :=
  Quot.liftOn₂ a b add_fn (add_respects_1) (add_respects_2)

instance : Add MyInt := ⟨MyInt.add⟩ -- interface

def mul_fn (a: myint) (b: myint) : MyInt :=
  (a.l*b.l+a.r*b.r)—(a.l*b.r+a.r*b.l)

private theorem mul_respects_nat_1 (a b a' b' c d : mynat) :
(myint.mk a b) ~ (myint.mk a' b') → mul_fn (myint.mk c d) (myint.mk a b) = mul_fn (myint.mk c d) (myint.mk a' b') := by {
  intro hab
  unfold mul_fn
  apply rel_nat_int
  ring
  rw [←left_distrib, ←left_distrib, add_assoc, ←left_distrib, add_assoc, mul_comm d b', ←right_distrib, add_comm b a', hab]
  rw [mul_comm d, mul_comm c]
}

private theorem mul_respects_nat_2 (a b a' b' c d : mynat) :
(myint.mk a b) ~ (myint.mk a' b') → mul_fn (myint.mk a b) (myint.mk c d) = mul_fn (myint.mk a' b') (myint.mk c d) := by {
  intro hab
  unfold mul_fn
  apply rel_nat_int
  ring
  rw [mul_comm c b', ←right_distrib, mul_comm b d, add_comm, ←add_assoc, add_comm, ←add_assoc, ←left_distrib, add_comm b a', hab]
  rw [←add_comm (d*b'), ←add_assoc, ←add_assoc, mul_comm d b', ←right_distrib, add_assoc, ←left_distrib, add_comm b' a, add_comm b a', hab]
  rw [mul_comm d, mul_comm c]
}

private theorem mul_respects_1 (a b₁ b₂ : myint) (hb: b₁ ~ b₂) : mul_fn a b₁ = mul_fn a b₂ := by {
  exact (mul_respects_nat_1 b₁.l b₁.r b₂.l b₂.r a.l a.r) hb
}

private theorem mul_respects_2 (a₁ a₂ b : myint) (ha: a₁ ~ a₂) : mul_fn a₁ b = mul_fn a₂ b := by {
  exact (mul_respects_nat_2 a₁.l a₁.r a₂.l a₂.r b.l b.r) ha
}

-- ｷﾀ━━━(ﾟ∀ﾟ)━━━!!
def mul (a : MyInt) (b : MyInt) : MyInt :=
  Quot.liftOn₂ a b mul_fn (mul_respects_1) (mul_respects_2)

instance : Mul MyInt := ⟨MyInt.mul⟩

theorem mul_nat {a b c d: mynat} : (a—b)*(c—d) = (a*c+b*d)—(a*d+b*c) := by rfl

def recurse (x : Nat) : MyInt :=
  if x = (0 : Nat) then
    0 — 0
  else
    recurse (x-(1 : Nat)) + (1 — 0)

instance : OfNat MyInt n where ofNat := recurse n

theorem zero_eq : 0 = 0 — 0 := by rfl
theorem one_eq : 1 = 1 — 0 := by rfl

def succ (a: MyInt) : MyInt := a + 1

def neg_fn (a: myint) : MyInt := (a.r—a.l)

-- (a b : α) → r a b → f a = f b
private theorem neg_respects_nat (a b a' b': mynat) : myint.mk a b ~ myint.mk a' b' → neg_fn (myint.mk a b) = neg_fn (myint.mk a' b') := by {
  intro hr
  apply rel_nat_int
  rw [add_comm, add_comm b' a]
  exact hr.symm
}
private theorem neg_respects (a a' : myint) (ha: a ~ a') : neg_fn a = neg_fn a' := by {
  exact (neg_respects_nat a.l a.r a'.l a'.r) ha
}

def neg (a : MyInt) : MyInt :=
  Quot.liftOn a neg_fn neg_respects

instance : Neg MyInt := ⟨MyInt.neg⟩ -- interface

theorem neg_nat (a b: mynat) : -(a—b) = (b—a) := by rfl

def of_mynat (a: mynat) : MyInt := (a — 0)

theorem zero_def : (0: MyInt) = (0 — 0) := by rfl

/-
private def add_fn (a: myint) (b: myint) : MyInt :=
  mk (a.l+b.l) (a.r+b.r)
-/

theorem add_nat {a b c d: mynat} : (a—b)+(c—d) = (a+c)—(b+d) := by rfl

theorem int_to_pair (a : MyInt) : ∃n m, n—m = a := by {
  rcases a with ⟨l, r⟩
  use l, r
  rfl
}

-- theorem add_cancel {a b c : mynat} (h1 : a+b = a+c) : b = c := by
theorem add_cancel {a b c : MyInt} (h1 : a+b = a+c) : b = c := by {
  rcases int_to_pair a with ⟨l, r, ha⟩
  rcases int_to_pair b with ⟨l', r', hb⟩
  rcases int_to_pair c with ⟨l'', r'', hc⟩
  rw [hb.symm, hc.symm]
  rw [ha.symm, hb.symm, hc.symm] at h1

  rw [add_nat, add_nat] at h1
  apply rel_nat_int

  have h2 := rel_int_nat h1
  rw [add_assoc, add_assoc] at h2
  have h3 := mynat.add_cancel (a := l) h2
  rw [←add_assoc, add_comm, ←add_assoc, add_comm, ←add_assoc, add_comm l'', add_assoc, add_assoc] at h3
  have h4 := mynat.add_cancel (a := r) h3
  rw [add_comm, add_comm r'] at h4
  exact h4
}

theorem add_cancel' {a b c : MyInt} : b = c → a+b = a+c := by {
  intro h
  rw [h]
}

theorem trichotomy (x: MyInt) : ∃ n > 0, x = 0 ∨ x = of_mynat n ∨ x = -of_mynat n := by {
  rcases int_to_pair x with ⟨a, b, hx⟩
  unfold of_mynat
  rw [zero_def]
  have tri := mynat.trichotomy a b
  cases tri with
  | inl h1 => {
    have h2 := (mynat.lt_neq_zero _ _).mp h1
    rcases h2 with ⟨c, hc1, hc2⟩
    use c
    constructor
    use c
    constructor; ring
    exact hc2.symm

    apply Or.inr
    apply Or.inr
    rw [neg_nat]
    have hr : 0 — c = x :=
      calc
        0 — c = a — (a+c) := by apply rel_nat_int; ring
        _ = a — b := by rw [hc1]
        _ = x := by rw [hx]

    exact hr.symm
  }
  | inr duo => {
    cases duo with
    | inl h1 => {
      use 1
      constructor
      use 1
      constructor; ring
      rw [mynat.one_eq_succ_zero]
      exact (mynat.succ_ne_zero 0).symm

      apply Or.inl
      rw [h1] at hx
      rw [hx.symm]
      apply rel_nat_int
      ring
    }
    | inr h1 => {
      have h2 := (mynat.lt_neq_zero _ _).mp h1
      rcases h2 with ⟨c, hc1, hc2⟩
      use c

      constructor
      use c
      constructor; ring
      exact hc2.symm

      apply Or.inr
      apply Or.inl
      rw [hx.symm]
      apply rel_nat_int
      rw [add_zero, add_comm c b]
      exact hc1
    }
  }
}

-- Proposition 4.1.6

-- you can do even better. make these macros all a single one
macro "myint_xyz" : tactic =>
  `(tactic| (intro x y z
             rcases int_to_pair x with ⟨a, b, hx⟩
             rcases int_to_pair y with ⟨c, d, hy⟩
             rcases int_to_pair z with ⟨e, f, hz⟩
             rw [hx.symm, hy.symm, hz.symm]
             apply rel_nat_int
             ring))

macro "myint_xy" : tactic =>
  `(tactic| (intro x y
             rcases int_to_pair x with ⟨a, b, hx⟩
             rcases int_to_pair y with ⟨c, d, hy⟩
             rw [hx.symm, hy.symm]
             apply rel_nat_int
             ring))

macro "myint_x" : tactic =>
  `(tactic| (intro x
             rcases int_to_pair x with ⟨a, b, hx⟩
             rw [hx.symm]
             apply rel_nat_int
             ring))

theorem add_comm : ∀ (x y : MyInt), x+y = y+x := by myint_xy
theorem add_assoc : ∀ (x y z  : MyInt), x+y+z = x+(y+z) := by myint_xyz
theorem add_zero : ∀ (x : MyInt), x + 0 = x := by myint_x
theorem zero_add : ∀ (x : MyInt), 0 + x = x := by myint_x
theorem mul_comm : ∀ (x y : MyInt), x*y = y*x := by myint_xy
theorem mul_assoc : ∀ (x y z  : MyInt), x*y*z = x*(y*z) := by myint_xyz
theorem mul_one : ∀ (x : MyInt), x * 1 = x := by myint_x
theorem one_mul : ∀ (x : MyInt), 1 * x = x := by myint_x
theorem left_distrib : ∀ (x y z  : MyInt), x*(y+z) = x*y+x*z := by myint_xyz
theorem right_distrib : ∀ (x y z  : MyInt), (x+y)*z = x*z+y*z := by myint_xyz

-- these are not in the book, but needed to be considered a commutative ring in mathlib
theorem zero_mul : ∀ (x : MyInt), 0 * x = 0 := by myint_x
theorem mul_zero : ∀ (x : MyInt), x * 0 = 0 := by myint_x
theorem add_left_neg : ∀ (a : MyInt), -a + a = 0 := by myint_x

instance : CommRing MyInt where
  add_comm := add_comm
  add_assoc := add_assoc
  add_zero := add_zero
  zero_add := zero_add
  mul_comm := mul_comm
  mul_assoc := mul_assoc
  mul_one := mul_one
  one_mul := one_mul
  left_distrib := left_distrib
  right_distrib := right_distrib
  -- these are not in the book
  zero_mul := zero_mul
  mul_zero := mul_zero
  add_left_neg := add_left_neg

theorem sub_nat {a b c d : mynat} : (a—b) - (c—d) = (a—b) + (d—c) := by rfl

-- theorem no_zero_divisors (n m : mynat) : n*m = 0 → n = 0 ∨ m = 0
-- Proposition 4.18
theorem no_zero_divisors (a b : MyInt) (h1: a*b = 0) : a = 0 ∨ b = 0 := by {
  have tri := trichotomy a
  rcases tri with ⟨n, hn, tri⟩
  rcases int_to_pair b with ⟨c, d, hb⟩
  rw [hb.symm]
  rw [hb.symm] at h1
  cases tri with
  | inl h2 => apply Or.inl; exact h2
  | inr duo => {
    cases duo with
    | inl h2 => {
      unfold of_mynat at h2
      rw [h2, mul_nat] at h1
      rw [h2]
      have h3 := rel_int_nat h1

      apply Or.inr
      apply rel_nat_int
      ring
      rw [mynat.zero_mul, mynat.zero_mul, mynat.zero_add, mynat.add_zero, mynat.add_zero, mynat.add_zero] at h3
      exact mynat.mul_cancel_right hn h3
    }
    | inr h2 => {
      unfold of_mynat at h2
      rw [neg_nat] at h2
      rw [h2, mul_nat] at h1
      rw [h2]
      rw [mynat.zero_mul, mynat.zero_add, mynat.zero_mul, mynat.zero_add] at h1
      have h3 := rel_int_nat h1

      apply Or.inr
      apply rel_nat_int
      ring
      rw [mynat.add_comm] at h3
      have h4 := mynat.mul_cancel_right hn (mynat.add_cancel h3)
      exact h4.symm
    }
  }
}

def le (a b : MyInt) : Prop :=  ∃ (c : mynat), b = a + of_mynat c
def lt (a b : MyInt) : Prop :=  ∃ (c : mynat), b = a + of_mynat c ∧ a ≠ b

instance : LE MyInt where le := le
instance : LT MyInt where lt := lt

theorem le_eq (a b : MyInt) : le a b = (a ≤ b) := by rfl
theorem lt_eq (a b : MyInt) : lt a b = (a < b) := by rfl

theorem a_gt_b_pos (a b: MyInt) : a > b ↔ a - b > 0 := by {
  constructor
  · intro h
    rcases h with ⟨c, h1, h2⟩
    rw [h1]
    ring
    use c
    constructor; ring
    intro h3; rw [h3.symm, add_zero] at h1; exact h2 h1.symm
  · intro h
    rcases h with ⟨c, h1, h2⟩
    rw [zero_add] at h1
    use c
    constructor; rw [h1.symm]; ring
    intro h3
    rw [h3] at h2
    have h4 : a-a = 0
    ·ring
    rw [h4.symm] at h2
    contradiction
}

/-

theorem le_def' {a b : MyInt} {c : mynat} : b = a + of_mynat c → a ≤ b := by {
  intro h
  use c
}

theorem add_lt (a b c : MyInt) : a < b → c + a < c + b := by {
  intro h
  rcases h with ⟨d, h1, h2⟩
  have h3 := le_def' h1
  have h4 := add_le_add_left c h3
  rcases h4 with ⟨e, h4⟩
  use e
  constructor
  use h4
  intro h5
  have h6 := add_cancel h5
  exact h2 h6
}
-/

theorem add_gt (a b c : MyInt) : a > b → a+c > b+c := by {
  intro h
  rcases h with ⟨d, h1, h2⟩
  rw [h1, a_gt_b_pos]
  ring
  have h3 := h2
  rw [h1] at h2
  unfold of_mynat at *
  have h4 : (d—0) = a - b := by rw [h1]; ring
  rw [h4]
  use d
  constructor; ring
  exact h4.symm
  intro h5
  rw [h5.symm] at h4
  rw [h4, add_zero] at h2
  contradiction
}

theorem le_trans (a b c : MyInt) : a ≤ b → b ≤ c → a ≤ c := by {
  intro h1 h2
  rcases h1 with ⟨d, h1⟩
  rcases h2 with ⟨e, h2⟩
  use d + e
  unfold of_mynat at *
  rw [h1, add_assoc, add_nat, mynat.add_zero] at h2
  exact h2
}

theorem mul_cancel_right {a b c : MyInt} (c_pos : c ≠ 0) : a*c = b*c → a = b := by {
  intro h1
  have tri := trichotomy c
  rcases tri with ⟨n, hn, tri⟩
  cases tri with
  | inl hc => contradiction
  | inr duo => {
    cases duo with
    | inl hc1 => {
      rcases int_to_pair c with ⟨d, e, hc2⟩
      unfold of_mynat at hc1
      rw [hc2.symm] at hc1
      rw [hc2.symm] at h1
      have hc3 := rel_int_nat hc1
      rw [mynat.add_zero] at hc3
      rw [hc1] at h1
      rcases int_to_pair a with ⟨f, g, ha⟩
      rcases int_to_pair b with ⟨h, i, hb⟩
      rw [ha.symm, hb.symm, mul_nat] at h1
      have h2 := rel_int_nat h1
      simp only [mynat.mul_zero, mynat.add_zero, mynat.zero_add, ←mynat.right_distrib] at h2
      have h3 := mynat.mul_cancel hn h2
      rw [ha.symm, hb.symm]
      apply rel_nat_int
      exact h3
    }
    | inr hc1 => {
      rcases int_to_pair c with ⟨d, e, hc2⟩
      unfold of_mynat at hc1
      rw [hc2.symm, neg_nat] at hc1
      rw [hc2.symm] at h1
      have hc3 := rel_int_nat hc1
      rw [mynat.zero_add] at hc3
      rw [hc1] at h1
      rcases int_to_pair a with ⟨f, g, ha⟩
      rcases int_to_pair b with ⟨h, i, hb⟩
      rw [ha.symm, hb.symm, mul_nat] at h1
      have h2 := rel_int_nat h1
      simp only [mynat.mul_zero, mynat.add_zero, mynat.zero_add, ←mynat.right_distrib] at h2
      have h3 := mynat.mul_cancel hn h2
      rw [ha.symm, hb.symm]
      apply rel_nat_int
      rw [mynat.add_comm h g, mynat.add_comm f i]
      exact h3.symm
    }
  }
}
theorem mul_cancel_left {a b c : MyInt} (c_pos : c ≠ 0) : c*a = c*b → a = b := by {
  intro h1
  rw [mul_comm, mul_comm c b] at h1
  exact mul_cancel_right c_pos h1
}

theorem mul_left {a b c : MyInt} : a = b → c*a = c*b := by {
  intro h
  rw [h]
}

theorem mul_right {a b c : MyInt} : a = b → a*c = b*c := by {
  intro h
  rw [h]
}
-- theorem mul_cancel {a b c : MyInt} (c_pos : c ≠ 0) : a*c = b*c → a = b
theorem le_pos_mul (a b c : MyInt) (h1: a > b) (c_pos: c > 0) : a*c > b*c := by {
  rcases h1 with ⟨d, h1, h2⟩
  rcases c_pos with ⟨c_nat, hc_nat, c_neq_zero⟩
  rw [zero_add] at hc_nat
  use c_nat * d
  unfold of_mynat at *
  constructor
  · rw [h1]
    ring
    apply add_cancel'
    rw [hc_nat, mul_nat]
    ring
  · intro h3
    have h4 := mul_cancel_right c_neq_zero.symm h3
    contradiction
}

theorem neg_eq_mul (a : MyInt) : -a = -1 * a := by {
  rcases int_to_pair a with ⟨b, c, ha⟩
  have h1 : 1 = 1 — 0 := by rfl
  rw [ha.symm]
  rw [neg_nat, h1, neg_nat, mul_nat]
  ring
}

theorem le_neg (a b : MyInt) (h1: a > b) : -a < -b := by {
  rcases h1 with ⟨d, h1, h2⟩
  use d
  constructor
  rw [h1]
  ring
  intro h3
  rw [neg_eq_mul, neg_eq_mul b] at h3
  have h4 := mul_cancel_left (by {
    intro h4
    have one_eq : 1 = 1 — 0 := by rfl
    have zero_eq : 0 = 0 — 0 := by rfl
    rw [one_eq, zero_eq, neg_nat] at h4
    have h5 := rel_int_nat h4
    rw [mynat.zero_add, mynat.zero_add, mynat.one_eq_succ_zero] at h5
    have h6 := mynat.succ_ne_zero 0
    exact h6 h5.symm
  }) h3
  exact h2 h4.symm
}

theorem trichotomy_rel (a : MyInt) : a > 0 ∨ a = 0 ∨ a < 0 := by {
  have tri_a := trichotomy a
  rcases tri_a with ⟨na, hna, tri_a⟩
  rcases tri_a with ⟨ha⟩ | ⟨⟨ha⟩ | ⟨ha⟩⟩
  apply Or.inr; apply Or.inl
  exact ha
  apply Or.inl
  use na
  constructor
  rw [zero_add]; exact ha
  intro ha'
  rw [ha'.symm] at ha
  have ha'' := rel_int_nat ha
  rw [mynat.zero_add, mynat.add_zero] at ha''
  rcases hna with ⟨_, _, haa⟩
  contradiction
  apply Or.inr; apply Or.inr
  use na
  constructor
  rw [ha]
  ring
  intro ha'
  rw [ha'] at ha
  have ha'' := rel_int_nat ha
  simp only at ha''
  rw [mynat.zero_add, mynat.add_zero] at ha''
  rcases hna with ⟨_, _, haa⟩
  exact haa ha''.symm
}

theorem neg_zero_eq_zero : -(0: MyInt) = 0 := by {
  ring
}

theorem order_trichotomy (a b : MyInt) : a < b ∨ a = b ∨ a > b := by {
  have tri_a := trichotomy a
  have tri_b := trichotomy b
  rcases tri_a with ⟨na, hna, tri_a⟩
  rcases tri_b with ⟨nb, hnb, tri_b⟩
  unfold of_mynat at *
  rw [neg_nat] at *

  rcases tri_a with ⟨ha⟩ | ⟨⟨ha⟩ | ⟨ha⟩⟩

  -- a = 0
  rcases tri_b with ⟨hb⟩ | ⟨⟨hb⟩ | ⟨hb⟩⟩
  -- b = 0
  apply Or.inr; apply Or.inl; rw [ha, hb]
  -- b > 0
  apply Or.inl
  rw [ha, hb]
  use nb
  constructor; rw [zero_add]; rfl
  intro h1
  have h2 := rel_int_nat h1
  rw [mynat.add_zero, mynat.add_zero] at h2
  rw [h2.symm] at hnb
  rcases hnb with ⟨_, _, _ ⟩
  contradiction
  -- b < 0
  apply Or.inr; apply Or.inr
  rw [ha, hb]
  use nb
  constructor; unfold of_mynat; rw [add_nat]; apply rel_nat_int; ring
  intro h1
  have h2 := rel_int_nat h1
  rw [mynat.zero_add, mynat.zero_add] at h2
  rw [h2.symm] at hnb
  rcases hnb with ⟨_, _, _ ⟩
  contradiction

  -- a > 0
  rcases tri_b with ⟨hb⟩ | ⟨⟨hb⟩ | ⟨hb⟩⟩
  -- b = 0
  apply Or.inr; apply Or.inr
  rw [ha, hb]
  use na
  constructor; unfold of_mynat; rw [zero_eq, add_nat]; apply rel_nat_int; ring
  intro h1
  have h2 := rel_int_nat h1
  rw [mynat.zero_add, mynat.add_zero] at h2
  rw [h2.symm] at hna
  rcases hna with ⟨_, _, _ ⟩
  contradiction

  -- b > 0
  rw [ha, hb]
  have tri := mynat.trichotomy na nb
  rcases tri with ⟨c, hc, hab⟩ | ⟨⟨hab⟩ | ⟨c, hc, hab⟩⟩
  -- lt
  apply Or.inl; rw [hc]; use c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero, mynat.add_zero, ← hc] at h2; contradiction
  -- eq
  apply Or.inr; apply Or.inl; apply rel_nat_int; ring; exact hab;
  -- gt
  apply Or.inr; apply Or.inr; use c; constructor; unfold of_mynat; rw [add_nat]; apply rel_nat_int; ring; exact hc;
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero, mynat.add_zero] at h2; contradiction;
  -- b < 0
  rw [ha, hb]
  have tri := mynat.trichotomy nb na
  rcases tri with ⟨c, hc, _⟩ | ⟨⟨hab⟩ | ⟨c, hc, _⟩⟩
  apply Or.inr; apply Or.inr; rw [hc]; use nb * 2 + c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero, mynat.add_comm, ← hc] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).left.symm; rcases hnb with ⟨_, _, _ ⟩; contradiction
  -- eq
  apply Or.inr; apply Or.inr; rw [hab]; use na * 2; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).left.symm; rcases hna with ⟨_, _, _ ⟩; contradiction
  -- gt
  apply Or.inr; apply Or.inr; rw [hc]; use na * 2 + c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).left.symm; rcases hna with ⟨_, _, _ ⟩; contradiction

  -- a < 0
  rcases tri_b with ⟨hb⟩ | ⟨⟨hb⟩ | ⟨hb⟩⟩
  -- b = 0
  apply Or.inl
  rw [ha, hb]
  use na
  constructor; unfold of_mynat; rw [zero_eq, add_nat]; apply rel_nat_int; ring
  intro h1
  have h2 := rel_int_nat h1
  rw [mynat.zero_add, mynat.zero_add] at h2
  rcases hna with ⟨_, _, _ ⟩; contradiction
  -- b > 0
  rw [ha, hb]
  have tri := mynat.trichotomy nb na
  rcases tri with ⟨c, hc, _⟩ | ⟨⟨hab⟩ | ⟨c, hc, _⟩⟩
  -- lt
  apply Or.inl; rw [hc]; use nb * 2 + c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero, mynat.add_comm, ← hc] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).left.symm; rcases hna with ⟨_, _, _ ⟩; contradiction
  -- eq
  apply Or.inl; rw [hab]; use na * 2; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).left.symm; rcases hna with ⟨_, _, _ ⟩; contradiction
  -- gt
  apply Or.inl; rw [hc]; use na * 2 + c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.add_zero] at h2;
  have h3 := (mynat.zero_iff_eq_zero _ _ h2.symm).right.symm; rcases hna with ⟨_, _, _ ⟩; contradiction

  -- b < 0
  rw [ha, hb]
  have tri := mynat.trichotomy na nb
  rcases tri with ⟨c, hc, hab⟩ | ⟨⟨hab⟩ | ⟨c, hc, hab⟩⟩
  -- lt
  apply Or.inr; apply Or.inr; rw [hc]; use c; constructor; apply rel_nat_int; ring
  intro h1; have h2 := rel_int_nat h1; rw [mynat.zero_add, mynat.zero_add, ← hc] at h2; contradiction
  -- eq
  apply Or.inr; apply Or.inl; apply rel_nat_int; ring; exact hab.symm;
  -- gt
  apply Or.inl; use c; constructor; unfold of_mynat; rw [add_nat]; apply rel_nat_int; ring; rw [mynat.add_comm]; exact hc;
  intro h1; have h2 := rel_int_nat h1; rw [mynat.zero_add, mynat.zero_add] at h2; contradiction;
}

-- extra stuff to prove it's a linear order for mathlib

theorem le_refl : ∀ (x : MyInt), x ≤ x := by {
  intro x
  use 0
  unfold of_mynat
  rcases int_to_pair x with ⟨a, b, hx⟩
  rw [hx.symm, add_nat]
  ring
}

-- theorem zero_iff_eq_zero (a b : mynat) : a+b = 0 → a = 0 ∧ b = 0
theorem le_antisymm : ∀ (x y : MyInt), x ≤ y → y ≤ x → x = y := by {
  intro x y h1 h2
  rcases h1 with ⟨a, hxy⟩
  rcases h2 with ⟨b, hyx⟩
  unfold of_mynat at *
  rcases int_to_pair y with ⟨y₁, y₂, hy⟩
  rcases int_to_pair x with ⟨x₁, x₂, hx⟩
  rw [hy.symm, hx.symm]
  rw [hy.symm, hx.symm, add_nat] at hxy
  rw [hy.symm, hx.symm, add_nat] at hyx
  apply rel_nat_int
  have h1 := rel_int_nat hxy
  have h2 := rel_int_nat hyx

  rw [mynat.add_zero] at *
  rw [h2, ← mynat.add_assoc y₁]
  apply mynat.add_cancel'
  rw [mynat.add_comm]
  nth_rw 2 [← mynat.add_zero x₂]
  apply mynat.add_cancel'
  rw [mynat.add_comm x₁, ← mynat.add_assoc, h2, mynat.add_assoc, mynat.add_assoc, mynat.add_comm a, ←mynat.add_assoc y₁ ] at h1
  nth_rw 1 [← mynat.add_zero y₁] at h1
  have h3 := mynat.add_cancel (mynat.add_cancel_right h1)
  have h4 := mynat.zero_iff_eq_zero a b h3.symm
  exact h4.right
}
theorem lt_to_le {a b: MyInt} (h: a < b) : a ≤ b := by {
  rcases h with ⟨c, h1⟩
  use c
  exact h1.left
}

theorem a_le_b_le_zero (a b: MyInt) : a ≤ b ↔ a - b ≤ 0 := by {
  constructor
  · intro h
    rcases h with ⟨c, h1⟩
    rw [h1]
    use c
    ring
  · intro h
    rcases h with ⟨c, h1⟩
    use c
    have h2 := add_cancel' (a := b) h1
    rw [add_zero] at h2
    rw [h2]
    ring
}

theorem add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt) : c + a ≤ c + b := by {
  rcases h with ⟨d, h⟩
  rw [h, a_le_b_le_zero]
  ring
  use d
  unfold of_mynat
  rw [neg_nat, add_nat]
  apply rel_nat_int
  ring
}

theorem zero_ne_one : (0 : MyInt) ≠ 1 := by {
    intro h1
    have h2 := rel_int_nat h1
    simp only at h2
}

theorem one_ne_zero : (1 : MyInt) ≠ 0 := by {
    exact zero_ne_one.symm
}

/-
type mismatch
  HEq.rfl
has type
  HEq ?m.109596 ?m.109596 : Prop
but is expected to have type
  a✝ < b✝ ↔ a✝ ≤ b✝ ∧ ¬b✝ ≤ a✝ : Prop
-/

theorem sub_eq_sub (a b: mynat) : (a—b) = of_mynat a - of_mynat b := by unfold of_mynat; rw [sub_nat, add_nat]; apply rel_nat_int; ring

def beq_fn (n m: myint): Bool := n.l+m.r = m.l+n.r

private theorem beq_respects_1 (a b₁ b₂ : myint) (hb: b₁ ~ b₂) : beq_fn a b₁ = beq_fn a b₂ := by {
  unfold rel_int at hb
  unfold beq_fn
  have dec := mynat.decEq (a.l + b₂.r) (b₂.l + a.r)
  rcases dec with ⟨h⟩ | ⟨h⟩

  rw [decide_eq_false h]
  apply decide_eq_false
  intro h'
  have h'' := mynat.add_cancel_right' (a := b₂.l) h'
  rw [← mynat.add_assoc, mynat.add_comm b₁.r, hb.symm, mynat.add_comm a.l, ← mynat.add_assoc, ← mynat.add_assoc, mynat.add_comm b₂.r, mynat.add_comm a.r] at h''
  have h''' := mynat.add_cancel h''
  contradiction

  rw [decide_eq_true h]
  apply decide_eq_true
  have h' := mynat.add_cancel_right' (a := b₁.l) h
  rw [← mynat.add_assoc, mynat.add_comm b₂.r, hb, mynat.add_comm a.l, ← mynat.add_assoc, ← mynat.add_assoc] at h'
  have h'' := mynat.add_cancel h'
  rw [mynat.add_comm, mynat.add_comm b₁.l]
  exact h''
}

private theorem beq_respects_2 (a₁ a₂ b : myint) (ha: a₁ ~ a₂) : beq_fn a₁ b = beq_fn a₂ b := by {
  unfold rel_int at ha
  unfold beq_fn
  have dec := mynat.decEq (a₂.l + b.r) (b.l + a₂.r)
  rcases dec with ⟨h⟩ | ⟨h⟩

  rw [decide_eq_false h]
  apply decide_eq_false
  intro h'
  have h'' := mynat.add_cancel' (a := a₂.r) h'
  rw [mynat.add_assoc, mynat.add_comm a₂.r, ha, mynat.add_comm a₂.l, mynat.add_comm a₂.r, mynat.add_comm b.l, ← mynat.add_assoc, ← mynat.add_assoc] at h''
  have h''' := mynat.add_cancel h''
  contradiction

  rw [decide_eq_true h]
  apply decide_eq_true
  have h' := mynat.add_cancel_right' (a := a₁.l) h
  rw [mynat.add_comm b.l, mynat.add_comm (a₂.r+b.l), mynat.add_assoc, ha, ← mynat.add_assoc, ← mynat.add_assoc] at h'
  have h'' := mynat.add_cancel h'
  rw [mynat.add_comm, mynat.add_comm b.l]
  exact h''
}

def beq (a b: MyInt) := Quot.liftOn₂ a b beq_fn (beq_respects_1) (beq_respects_2)

instance : BEq MyInt where
  beq := MyInt.beq

-- n.l+m.r = m.l+n.r
theorem beq_nat {a b c d: mynat} : beq (a—b) (c—d) = Decidable.decide (a+d = c+b) := by rfl

theorem eq_of_beq_eq_true {n m : MyInt} : Eq (beq n m) true → Eq n m := by {
  intro h
  rcases int_to_pair n with ⟨a, b, hn⟩
  rcases int_to_pair m with ⟨c, d, hm⟩
  rw [hn.symm, hm.symm]
  rw [hn.symm, hm.symm, beq_nat] at h
  have h' := of_decide_eq_true h
  apply rel_nat_int
  exact h'
}

theorem ne_of_beq_eq_false {n m : MyInt} : Eq (beq n m) false → Not (Eq n m) := by {
  intro h
  rcases int_to_pair n with ⟨a, b, hn⟩
  rcases int_to_pair m with ⟨c, d, hm⟩
  rw [hn.symm, hm.symm]
  rw [hn.symm, hm.symm, beq_nat] at h
  have h' := of_decide_eq_false h
  intro h2
  have h2' := rel_int_nat h2
  contradiction
}

def decEq (n m : MyInt) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false  => isFalse (ne_of_beq_eq_false h)

@[inline] instance : DecidableEq MyInt := MyInt.decEq

/-
  I had to manually sift through the code, the error is with lt_iff_le_not_le
-/
instance : LinearOrderedCommRing MyInt where
  le_trans := le_trans
  le_refl := le_refl
  le_antisymm := le_antisymm
  add_le_add_left := add_le_add_left
  exists_pair_ne := by {
    use 0, 1
    exact zero_ne_one
  }
  zero_le_one := by {
    use 1
    ring
  }
  mul_pos := by {
    intro x y h1 h2
    rcases h1 with ⟨a, h1, h1'⟩
    rcases h2 with ⟨b, h2, h2'⟩
    rw [zero_add] at *
    unfold of_mynat at *
    rw [h1, h2, mul_nat]
    ring
    use a*b
    constructor
    unfold of_mynat
    apply rel_nat_int
    ring
    intro h3
    have h4 := rel_int_nat h3
    rw [mynat.add_zero, mynat.add_zero] at h4
    have h5 := mynat.no_zero_divisors a b h4.symm
    rw [zero_eq] at *
    cases h5 with
    | inl h5 => rw [h5] at h1; rw [h1] at h1'; contradiction
    | inr h5 => rw [h5] at h2; rw [h2] at h2'; contradiction
  }
  le_total := by {
    intro x y
    have h1 := order_trichotomy x y
    cases h1 with
    | inl h1 => apply Or.inl; rcases h1 with ⟨a, h1, h1'⟩; use a
    | inr duo => cases duo with
    | inl h1 => apply Or.inl; use 0; unfold of_mynat; rw [← zero_eq, add_zero]; exact h1.symm
    | inr h1 => apply Or.inr; rcases h1 with ⟨a, h1, h1'⟩; use a
  }
  decidableLE := by {
    intro a b
    simp
    sorry
  }
  mul_comm := mul_comm
  lt_iff_le_not_le := by {
    intro a b
    constructor
    intro h
    rcases h with ⟨c, h, h'⟩
    constructor
    use c
    intro h2
    rw [h] at h'
    rcases h2 with ⟨d, h2, h2'⟩
    rw [← add_zero b, add_assoc, add_assoc] at h
    have h1' := add_cancel h
    unfold of_mynat at h1'
    rw [zero_add, zero_eq, add_nat] at h1'
    have h1'' := rel_int_nat h1'
    rw [mynat.zero_add, mynat.zero_add, mynat.add_zero] at h1''
    rcases mynat.zero_iff_eq_zero _ _ h1''.symm with ⟨h2, h2'⟩
    unfold of_mynat at h'
    rw [h2, h2', zero_eq.symm, add_zero, add_zero] at h'
    contradiction

    intro h
    rcases h with ⟨h1, h2⟩
    rcases h1 with ⟨c, h⟩
    use c
    constructor
    exact h
    intro h1
    rw [h1] at h2
    have obvious : b ≤ b := by {
      use 0
      unfold of_mynat
      rw [zero_eq.symm, add_zero]
    }
    contradiction
  }

/-
xy: MyInt
h1: 0 < x
h2: 0 < y
⊢ 0 < x * y
-/
theorem mul_pos (x y: MyInt) (h1: 0 < x) (h2: 0 < y) : 0 < x * y := by {
    rcases h1 with ⟨a, h1, h1'⟩
    rcases h2 with ⟨b, h2, h2'⟩
    rw [zero_add] at *
    unfold of_mynat at *
    rw [h1, h2, mul_nat]
    ring
    use a*b
    constructor
    unfold of_mynat
    apply rel_nat_int
    ring
    intro h3
    have h4 := rel_int_nat h3
    rw [mynat.add_zero, mynat.add_zero] at h4
    have h5 := mynat.no_zero_divisors a b h4.symm
    rw [zero_eq] at *
    cases h5 with
    | inl h5 => rw [h5] at h1; rw [h1] at h1'; contradiction
    | inr h5 => rw [h5] at h2; rw [h2] at h2'; contradiction
}

-- why can't linarith infer this??
theorem ge_pos {a b: MyInt} (h1: a ≥ 0) (h2: b ≥ 0) : a*b ≥ 0 := by {
  rcases h1 with ⟨c, h1, h1'⟩
  rcases h2 with ⟨d, h2, h2'⟩
  unfold of_mynat
  ring
  rw [mul_nat]
  use c*d
  unfold of_mynat
  ring
}

theorem gt_pos {a b: MyInt} (h1: a > 0) (h2: b > 0) : a*b > 0 := by {
  rcases h1 with ⟨c, h1, h1'⟩
  rcases h2 with ⟨d, h2, h2'⟩
  rw [h1, h2]
  unfold of_mynat
  ring
  rw [mul_nat]
  use c*d
  unfold of_mynat
  constructor
  ring
  ring
  intro h3
  rw [zero_eq] at  h3
  have h4 := rel_int_nat h3
  rw [mynat.zero_add, mynat.add_zero] at h4
  rcases mynat.no_zero_divisors _ _ h4.symm with ⟨hc⟩ | ⟨hd⟩
  rw [hc, zero_add] at h1
  unfold of_mynat at h1
  rw [zero_eq.symm] at h1
  exact h1'.symm h1

  rw [hd, zero_add] at h2
  unfold of_mynat at h2
  rw [zero_eq.symm] at h2
  exact h2'.symm h2
}

end MyInt
