import Std.Tactic.RCases
import Mathlib.Tactic.Use
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LibrarySearch
import Tao4.Natural
import Tao4.Integer

structure myrat where
  mk ::
  n : MyInt
  d : MyInt
  d_neq : d ≠ 0

def rel_rat (a: myrat) (b: myrat) : Prop := a.n*b.d = b.n*a.d

theorem rel_rat_refl : ∀ x, rel_rat x x := by {
  intro x
  constructor
}

theorem rel_rat_symm : ∀ {x y}, rel_rat x y → rel_rat y x := by {
  intro x y h1
  unfold rel_rat
  rw [h1]
}

theorem rel_rat_trans : ∀ {x y z}, rel_rat x y → rel_rat y z → rel_rat x z := by {
  intros x y z
  intro h_xy
  intro h_yz
  unfold rel_rat at *
  apply MyInt.mul_cancel_left y.d_neq
  rw [←MyInt.mul_assoc, MyInt.mul_comm y.d, h_xy, MyInt.mul_assoc, MyInt.mul_comm x.d, ←MyInt.mul_assoc, h_yz]
  ring
}

private theorem is_equivalence_rat : Equivalence rel_rat where
  refl := rel_rat_refl
  symm := rel_rat_symm
  trans := rel_rat_trans

instance myratSetoid : Setoid (myrat) where
  r     := rel_rat
  iseqv := is_equivalence_rat

def MyRat := Quotient myratSetoid

namespace MyRat

def mk (n d : MyInt) (d_neq : d ≠ 0) : MyRat := Quotient.mk' (myrat.mk n d d_neq)

-- this is \em
infixl:65 " // "   => mk
infixl:65 " ~ "   => rel_rat

-- very useful
theorem rel_int_rat {a b c d: MyInt} {hb: b ≠ 0} {hd: d ≠ 0} : a*d = c*b → (a // b) hb = (c // d) hd := by {
  intro h
  apply Quot.sound (r := rel_rat); unfold rel_rat
  exact h
}

theorem rel_rat_int {a b c d: MyInt} {hb: b ≠ 0} {hd: d ≠ 0} : (a // b) hb = (c // d) hd → a*d = c*b := by {
  intro h
  have h1 := Quotient.exact h
  exact h1
}

theorem mul_neq_zero {a b: MyInt} (a_neq: a ≠ 0) (b_neq: b ≠ 0) : a * b ≠ 0 := by {
  intro h1
  have h2 := MyInt.no_zero_divisors a b h1
  rcases h2 with ⟨h2⟩ | ⟨h2⟩
  exact a_neq h2
  exact b_neq h2
}

private def add_fn (x: myrat) (y: myrat) : MyRat :=
  ((x.n*y.d+x.d*y.n) // (x.d*y.d)) (mul_neq_zero x.d_neq y.d_neq)


private theorem add_respects_1 (a b₁ b₂ : myrat) (hb: b₁ ~ b₂) : add_fn a b₁ = add_fn a b₂ := by {
  unfold add_fn
  unfold rel_rat at hb
  apply rel_int_rat
  ring
  rw [mul_assoc (a.d^2), hb]
  ring
}

private theorem add_respects_2 (a₁ a₂ b : myrat) (ha: a₁ ~ a₂) : add_fn a₁ b = add_fn a₂ b := by {
  unfold add_fn
  unfold rel_rat at ha
  apply rel_int_rat
  ring
  rw [mul_comm _ a₂.d, ←mul_assoc, mul_comm a₂.d, ha]
  ring
}

def add (a : MyRat) (b : MyRat) : MyRat :=
  Quot.liftOn₂ a b add_fn (add_respects_1) (add_respects_2)

instance : Add MyRat := ⟨MyRat.add⟩ -- interface

theorem add_int {a b c d: MyInt} {b_neq : b ≠ 0} {d_neq : d ≠ 0} : (a // b) b_neq + (c // d) d_neq = ((a*d+b*c) // (b*d)) (mul_neq_zero b_neq d_neq) := by rfl

def mul_fn (x: myrat) (y: myrat) : MyRat :=
  ((x.n*y.n) // (x.d*y.d)) (mul_neq_zero x.d_neq y.d_neq)

private theorem mul_respects_1 (a b₁ b₂ : myrat) (hb: b₁ ~ b₂) : mul_fn a b₁ = mul_fn a b₂ := by {
  unfold mul_fn; unfold rel_rat at hb; apply rel_int_rat
  ring
  rw [mul_comm a.n, mul_comm _ b₂.d, ← mul_assoc, ← mul_assoc, mul_comm b₂.d, hb]
  ring
}

private theorem mul_respects_2 (a₁ a₂ b : myrat) (ha: a₁ ~ a₂) : mul_fn a₁ b = mul_fn a₂ b := by {
  unfold mul_fn; unfold rel_rat at ha; apply rel_int_rat
  ring
  rw [mul_comm _ a₂.d, ← mul_assoc, mul_comm a₂.d, ha]
  ring
}

def mul (a : MyRat) (b : MyRat) : MyRat :=
  Quot.liftOn₂ a b mul_fn (mul_respects_1) (mul_respects_2)

instance : Mul MyRat := ⟨MyRat.mul⟩

theorem mul_int {a b c d: MyInt} {b_neq : b ≠ 0} {d_neq : d ≠ 0} : (a // b) b_neq * (c // d) d_neq = ((a*c) // (b*d)) (mul_neq_zero b_neq d_neq) := by rfl

theorem rat_destruct (a : MyRat) : ∃(n m : MyInt) (m_neq: m ≠ 0), (n // m) (m_neq) = a := by {
  rcases a with ⟨n, m, m_neq⟩
  use n, m, m_neq
  rfl
}

def recurse (x : Nat) : MyRat :=
  if x = (0 : Nat) then
    (0 // 1) MyInt.one_ne_zero
  else
    recurse (x-(1 : Nat)) + (1 // 1) MyInt.one_ne_zero

instance : OfNat MyRat n where ofNat := recurse n

theorem zero_eq : 0 = (0 // 1) MyInt.one_ne_zero := by rfl
theorem one_eq : 1 = (1 // 1) MyInt.one_ne_zero := by rfl

def succ (a: MyRat) : MyRat := a + 1

def neg_fn (a: myrat) : MyRat := (-a.n // a.d) a.d_neq

private theorem neg_respects (a a' : myrat) (ha: a ~ a') : neg_fn a = neg_fn a' := by {
  unfold neg_fn
  unfold rel_rat at ha
  apply rel_int_rat
  rw [neg_mul, neg_mul, ha]
}

def neg (a : MyRat) : MyRat :=
  Quot.liftOn a neg_fn neg_respects

instance : Neg MyRat := ⟨MyRat.neg⟩

theorem zero_divided (m : MyInt) (m_neq : m ≠ 0): (0 // m) m_neq = 0 := by {
    rw [zero_eq]
    apply rel_int_rat
    ring
  }

theorem neq_num_neq_zero (x: MyRat) (ha: x ≠ 0) : ∀(n m : MyInt) (hm: m ≠ 0), (n // m) hm = x → n ≠ 0 := by {
  intro n m m_neq hm
  intro hn
  rw [hn] at hm
  have h1 : (0 // m) m_neq = 0 := by {
    rw [zero_eq]
    apply rel_int_rat
    ring
  }
  rw [h1] at hm
  exact ha hm.symm
}

def of_myint (a: MyInt) : MyRat := (a // 1) MyInt.one_ne_zero


theorem neq_num_neq_zero' {a b: MyInt} (b_neq : b ≠ 0) (a_neq : a ≠ 0) : (a // b) b_neq ≠ 0 := by {
  rw [zero_eq] at *
  intro h
  have h2 := rel_rat_int h
  simp at h2
  contradiction
}

def inv_fn (a: myrat) : MyRat := if h: (a.n = 0) then (0 // 1) (MyInt.one_ne_zero) else (a.d // a.n) h

private theorem inv_respects (a a' : myrat) (haa': a ~ a') : inv_fn a = inv_fn a' := by {
  unfold rel_rat at haa'
  unfold inv_fn

  have ad_neq := a.d_neq
  have a'd_neq := a'.d_neq

  split
  · case inl h => {
    rw [h, zero_mul] at haa'
    split
    · case inl h' => rfl
    · case inr h' => {
      have ha' := MyInt.no_zero_divisors a'.n a.d haa'.symm
      rcases ha' with ⟨h''⟩ | ⟨h''⟩
      contradiction
      contradiction
    }
  }
  · case inr h => {
    split
    · case inl h' => {
      rw [h', zero_mul] at haa'
      have ha' := MyInt.no_zero_divisors a.n a'.d haa'
      rcases ha' with ⟨h''⟩ | ⟨h''⟩
      contradiction
      contradiction
    }
    · case inr h' => {
      apply rel_int_rat
      rw [mul_comm a'.n] at haa'
      rw [haa'.symm]
      ring
    }
  }
}

/-
  after looking around, other people seem to avoid this problem by doing the following:
  · define the inverse function for a zero casem this is what the stdlib and some other people do and makes it more ergonomic as it doesn't need to carry the ≠0 everywhere
  · not using Quot and using a ≃ equivalence everywhere, this is what lean4-axiomatic does and from this it's naturally possible to do everything but that doesn't seem practical and would change pretty much everything (rw, etc)

  I really like the second solution, but for now I think I'll hold off from it and just do the cases version.
-/
def inv (a: MyRat) : MyRat :=
  Quot.liftOn a inv_fn inv_respects

instance : Inv MyRat := ⟨MyRat.inv⟩

theorem inv_int_bare {a b: MyInt} {b_neq : b ≠ 0} : ((a // b) b_neq) ⁻¹ = if h: (a = 0) then (0 // 1) (MyInt.one_ne_zero) else (b // a) h := by rfl
theorem inv_int {a b: MyInt} {b_neq : b ≠ 0} {a_neq : a ≠ 0} : ((a // b) b_neq) ⁻¹ = (b // a) a_neq := by {
  rw [inv_int_bare]
  split
  contradiction
  rfl
}

theorem cancel (a : MyRat) (ha: a ≠ 0): a*a⁻¹ = 1 := by {
  rcases rat_destruct a with ⟨n, m, m_neq, h1⟩
  have n_neq := neq_num_neq_zero a ha n m m_neq h1
  simp_rw [h1.symm]
  rw [inv_int, mul_int]
  apply rel_int_rat
  ring
  exact n_neq
}

macro "myrat_xyz" : tactic =>
  `(tactic| (intro x y z
             rcases rat_destruct x with ⟨a, b, b_neq, hx⟩
             rcases rat_destruct y with ⟨c, d, d_neq, hy⟩
             rcases rat_destruct z with ⟨e, f, f_neq, hz⟩
             rw [hx.symm, hy.symm, hz.symm]
             apply rel_int_rat
             ring))

macro "myrat_xy" : tactic =>
  `(tactic| (intro x y
             rcases rat_destruct x with ⟨a, b, b_neq, hx⟩
             rcases rat_destruct y with ⟨c, d, d_neq, hy⟩
             rw [hx.symm, hy.symm]
             apply rel_int_rat
             ring))

macro "myrat_x" : tactic =>
  `(tactic| (intro x
             rcases rat_destruct x with ⟨a, b, b_neq, hx⟩
             rw [hx.symm]
             apply rel_int_rat
             ring))

theorem add_comm : ∀ (x y : MyRat), x+y = y+x := by myrat_xy
theorem add_assoc : ∀ (x y z  : MyRat), x+y+z = x+(y+z) := by myrat_xyz
theorem add_zero : ∀ (x : MyRat), x + 0 = x := by myrat_x
theorem zero_add : ∀ (x : MyRat), 0 + x = x := by myrat_x
theorem mul_comm : ∀ (x y : MyRat), x*y = y*x := by myrat_xy
theorem mul_assoc : ∀ (x y z  : MyRat), x*y*z = x*(y*z) := by myrat_xyz
theorem mul_one : ∀ (x : MyRat), x * 1 = x := by myrat_x
theorem one_mul : ∀ (x : MyRat), 1 * x = x := by myrat_x
theorem left_distrib : ∀ (x y z  : MyRat), x*(y+z) = x*y+x*z := by myrat_xyz
theorem right_distrib : ∀ (x y z  : MyRat), (x+y)*z = x*z+y*z := by myrat_xyz

-- these are not in the book, but needed to be considered a commutative ring in mathlib
theorem zero_mul : ∀ (x : MyRat), 0 * x = 0 := by myrat_x
theorem mul_zero : ∀ (x : MyRat), x * 0 = 0 := by myrat_x
theorem add_left_neg : ∀ (a : MyRat), -a + a = 0 := by myrat_x

instance : CommRing MyRat where
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

-- can't actually show it's a field in mathlib, because in mathlib 0⁻¹ = 0

def div (a : MyRat) (b : MyRat): MyRat :=
  a * b ⁻¹

instance : Div MyRat := ⟨MyRat.div⟩

def Positive (a : MyRat) := ∃ (x y : MyInt) (y_pos: y ≠ 0), x ≥ 0 ∧ y > 0 ∧ a = (x // y) (y_pos)
def Negative (a : MyRat) := ∃ (b : MyRat), Positive b ∧ a = -b

theorem is_pos (n m: MyInt) (m_neq: m ≠ 0) (ha: n > 0) (hb: m > 0) : Positive ((n // m) m_neq) := by {
  unfold Positive;
  use n, m, m_neq
  constructor
  exact MyInt.lt_to_le ha
  constructor
  exact hb
  rfl
}

theorem cancel_int (n m: MyInt) (m_neg_neq: -m ≠ 0) (m_neq: m ≠ 0) : (-n // -m) m_neg_neq = (n // m) m_neq := by {
  apply rel_int_rat
  ring
}

theorem trichotomy (a : MyRat) : (Positive a) ∨ (a = 0) ∨ (Negative a)  := by {
  rcases rat_destruct a with ⟨n, m, m_neq, h1⟩
  have m_neg_neq : (-1: MyInt) ≠ 0 := by {
    intro h
    rw [MyInt.one_eq, MyInt.zero_eq] at h
    have a := MyInt.rel_int_nat h
    simp only at a
  }
  have m_neg_neq : -m ≠ 0 := by {
    intro h;
    rw [MyInt.neg_eq_mul, ← MyInt.neg_zero_eq_zero, MyInt.neg_eq_mul 0] at h
    have h' := MyInt.mul_cancel_left m_neg_neq h
    contradiction
  }
  rw [h1.symm, zero_eq]

  have tri_n := MyInt.trichotomy_rel n
  have tri_m := MyInt.trichotomy_rel m

  rcases tri_n with ⟨hn⟩ | ⟨⟨hn⟩ | ⟨hn⟩⟩
  rcases tri_m with ⟨hm⟩ | ⟨⟨hm⟩ | ⟨hm⟩⟩

  apply Or.inl
  exact is_pos n m m_neq hn hm

  contradiction

  apply Or.inr; apply Or.inr
  unfold Negative;

  have hm' := MyInt.le_neg 0 m hm
  rw [MyInt.neg_zero_eq_zero] at hm'
  have hb := is_pos n (-m) m_neg_neq hn hm'
  use (n // -m) m_neg_neq

  constructor
  assumption
  apply rel_int_rat
  simp only
  ring

  apply Or.inr; apply Or.inl
  rw [hn]
  exact zero_divided _ _

  rcases tri_m with ⟨hm⟩ | ⟨⟨hm⟩ | ⟨hm⟩⟩

  apply Or.inr; apply Or.inr
  unfold Negative;
  have hn' := MyInt.le_neg 0 n hn
  rw [MyInt.neg_zero_eq_zero] at hn'
  have hb := is_pos (-n) m m_neq hn' hm
  use ((-n) // m) m_neq
  constructor
  assumption
  apply rel_int_rat
  simp only
  ring

  contradiction

  apply Or.inl
  have hn' := MyInt.le_neg 0 n hn
  have hm' := MyInt.le_neg 0 m hm
  rw [MyInt.neg_zero_eq_zero] at hn'
  rw [MyInt.neg_zero_eq_zero] at hm'
  have hb := is_pos (-n) (-m) m_neg_neq hn' hm'
  rw [cancel_int n m m_neg_neq m_neq] at hb
  assumption
}

def lt (x y : MyRat) : Prop := Negative (x - y)
def le (x y : MyRat) : Prop := lt x y ∨ x = y

instance : LE MyRat where le := le
instance : LT MyRat where lt := lt

theorem lt_is_neg (a b : MyRat) (h: a < b) : Negative (a - b) := by exact h
theorem lt_is_neg' (a b : MyRat) (h: Negative (a - b)) : a < b := by exact h

theorem ge (a b : MyRat) (h: a > b) : b < a := by exact h
theorem ge' (a b : MyRat) (h: b < a) : a > b := by exact h

theorem pos_neg (a : MyRat) (h: Positive (-a)) : Negative a := by {
  use -a
  constructor
  exact h
  ring
}

theorem neg_pos (a : MyRat) (h: Negative (-a)) : Positive a := by {
  rcases h with ⟨a', pos_a, ha'⟩
  simp at ha'
  rw [ha']
  assumption
}
theorem order_trichotomy (a b : MyRat) : a = b ∨ a < b ∨ a > b := by {
  have tri := trichotomy (a - b)
  have h_neg : a - b = -(b -a)
  · ring
  rcases tri with ⟨h1⟩ | ⟨⟨h1⟩ | ⟨h1⟩⟩
  -- a-b > 0
  apply Or.inr; apply Or.inr
  apply ge'
  apply lt_is_neg'
  rw [h_neg] at h1
  exact pos_neg _ h1
  -- a-b = 0
  apply Or.inl
  apply add_right_cancel (b := -b)
  ring
  exact h1
  -- a-b < 0
  apply Or.inr; apply Or.inl
  exact h1
}

-- Proposition 4.2.9 (b)
theorem ge_pos (x y : MyRat) (h: x < y) : Positive (y-x) := by {
  rcases h with ⟨a', pos_a, ha'⟩
  apply neg_pos
  ring
  rw [sub_eq_add_neg, add_comm] at ha'
  rw [ha']
  apply pos_neg
  ring
  assumption
}

theorem pos_eq (x : MyRat)  (h: Positive x) : x > 0 := by {
  use x
  constructor
  exact h
  ring
}

theorem pos_eq' (x : MyRat)  (h: x > 0) : Positive x := by {
  rcases h with ⟨a', pos_a, ha'⟩
  simp at ha'
  rw [ha'.symm] at pos_a
  exact pos_a
}

-- def Positive (a : MyRat) := ∃ (x y : MyInt) (y_pos: y ≠ 0), x ≥ 0 ∧ y > 0 ∧ a = (x // y) (y_pos)
theorem le_trans (x y z : MyRat) (h1: x < y) (h2: y < z) : x < z := by {
  rcases h1 with ⟨a', pos_a, ha'⟩
  rcases h2 with ⟨b', pos_b, hb'⟩
  use (a'+b')
  constructor

  rcases pos_a with ⟨c, d, d_neq, c_ge, d_gt, ha⟩
  rcases pos_b with ⟨e, f, f_neq, e_ge, f_gt, hb⟩

  use c*f + e*d, d*f, (mul_neq_zero d_neq f_neq)
  have f_ge : f ≥ 0 := by {
    linarith
  }
  have d_ge : d ≥ 0 := by {
    linarith
  }

  constructor

  have ccc : c*f ≥ 0 := by {
    exact MyInt.ge_pos c_ge f_ge
  }

  have ccc : e*d ≥ 0 := by {
    exact MyInt.ge_pos e_ge d_ge
  }

  linarith
  constructor
  exact MyInt.mul_pos _ _ d_gt f_gt
  rw [ha, hb, add_int]
  ring
  ring
  rw [sub_eq_add_neg, sub_eq_add_neg, ha'.symm, hb'.symm]
  ring
}

theorem add_right_le (x y z: MyRat) (h1: x < y) : x+z < y+z := by {
  rcases h1 with ⟨a', pos_a, ha'⟩
  use a', pos_a
  rw [ha'.symm]
  ring
}

theorem le_neg (a b : MyRat) (h1: a > b) : -a < -b := by {
  rcases h1 with ⟨a', pos_a, ha'⟩
  use a', pos_a
  rw [ha'.symm]
  ring
}

theorem zero_mul_le (a b : MyRat) (h1: a > 0) (h2: b > 0) : a*b > 0 := by {
  have h3 := pos_eq' _ h1
  have h4 := pos_eq' _ h2
  rcases h3 with ⟨c, d, d_pos, c_ge, d_gt, ha⟩
  rcases h4 with ⟨n, m, m_neq, n_ge, m_gt, hb⟩
  apply pos_eq
  unfold Positive
  use c*n, d*m, mul_neq_zero d_pos m_neq
  use MyInt.ge_pos c_ge n_ge, MyInt.gt_pos d_gt m_gt
  rw [ha, hb, mul_int]
}

theorem mul_right_le (x y z: MyRat) (h1: x < y) (h2: z > 0): x*z < y*z := by {
  rcases h1 with ⟨a', pos_a, ha1⟩
  use y*z-x*z, by {
    apply pos_eq'
    have ha2 := le_neg _ _ (pos_eq a' pos_a)
    rw [ha1.symm] at ha2
    have h3 := le_neg _ _ ha2
    simp at h3
    rcases h3 with ⟨b', _, hb'⟩
    simp at hb'
    have ha3 := le_neg _ _ ha2
    simp at ha3
    have ha4 := zero_mul_le _ _ ha3 h2
    rw [← mul_sub_right_distrib]
    exact ha4
  }
  ring
}

-- next step is absolute value, this will be hard, as you will have to make it decidable

def beq_fn (a b: myrat): Bool := a.n*b.d = b.n*a.d

private theorem beq_respects_1 (a b₁ b₂ : myrat) (hb: b₁ ~ b₂) : beq_fn a b₁ = beq_fn a b₂ := by {
  unfold rel_rat at hb
  unfold beq_fn
  have dec := MyInt.decEq (a.n * b₂.d) (b₂.n * a.d)
  rcases dec with ⟨h⟩ | ⟨h⟩

  rw [decide_eq_false h]
  apply decide_eq_false
  intro h'
  have h'' := MyInt.mul_cancel_right' (c := b₂.d) h'
  rw [MyInt.mul_assoc, MyInt.mul_assoc, MyInt.mul_comm a.d, ← MyInt.mul_assoc, ← MyInt.mul_assoc, hb, MyInt.mul_comm a.n, MyInt.mul_comm b₂.n, MyInt.mul_assoc, MyInt.mul_assoc] at h''
  have h''' := MyInt.mul_cancel_left b₁.d_neq h''
  contradiction

  rw [decide_eq_true h]
  apply decide_eq_true
  have h' := MyInt.mul_cancel_right' (c := b₁.d) h
  rw [MyInt.mul_assoc, MyInt.mul_assoc, MyInt.mul_comm a.d, ← MyInt.mul_assoc, ← MyInt.mul_assoc, hb.symm, MyInt.mul_comm a.n, MyInt.mul_comm b₁.n, MyInt.mul_assoc, MyInt.mul_assoc] at h'
  have h'' := MyInt.mul_cancel_left b₂.d_neq h'
  assumption
}

private theorem beq_respects_2 (a₁ a₂ b : myrat) (ha: a₁ ~ a₂) : beq_fn a₁ b = beq_fn a₂ b := by {
  unfold rel_rat at ha
  unfold beq_fn
  have dec := MyInt.decEq (a₂.n * b.d) (b.n * a₂.d)
  rcases dec with ⟨h⟩ | ⟨h⟩

  rw [decide_eq_false h]
  apply decide_eq_false
  intro h'
  have h'' := MyInt.mul_cancel_right' (c := a₂.d) h'
  rw [MyInt.mul_assoc, MyInt.mul_assoc, MyInt.mul_comm b.d, ← MyInt.mul_assoc, ← MyInt.mul_assoc, ha, MyInt.mul_comm b.n, MyInt.mul_comm a₂.n, MyInt.mul_assoc, MyInt.mul_assoc] at h''
  have h''' := MyInt.mul_cancel_left a₁.d_neq h''
  contradiction

  rw [decide_eq_true h]
  apply decide_eq_true
  have h' := MyInt.mul_cancel_right' (c := a₁.d) h
  rw [MyInt.mul_assoc, MyInt.mul_assoc, MyInt.mul_comm b.d, ← MyInt.mul_assoc, ← MyInt.mul_assoc, ha.symm, MyInt.mul_comm b.n, MyInt.mul_comm a₁.n, MyInt.mul_assoc, MyInt.mul_assoc] at h'
  have h'' := MyInt.mul_cancel_left a₂.d_neq h'
  assumption
}

def beq (a b: MyRat) := Quot.liftOn₂ a b beq_fn (beq_respects_1) (beq_respects_2)

instance : BEq MyRat where
  beq := MyRat.beq

-- n.l+m.r = m.l+n.r
theorem beq_nat {a b c d: MyInt} {b_neq : b ≠ 0} {d_neq : d ≠ 0} : beq ((a // b) b_neq) ((c // d) d_neq) = Decidable.decide (a*d = c*b) := by rfl

theorem eq_of_beq_eq_true {n m : MyRat} : Eq (beq n m) true → Eq n m := by {
  intro h
  -- rcases rat_destruct a with ⟨n, m, m_neq, h1⟩
  rcases rat_destruct n with ⟨a, b, b_neq, hn⟩
  rcases rat_destruct m with ⟨c, d, d_neq, hm⟩
  rw [hn.symm, hm.symm]
  rw [hn.symm, hm.symm, beq_nat] at h
  have h' := of_decide_eq_true h
  apply rel_int_rat
  exact h'
}

theorem ne_of_beq_eq_false {n m : MyRat} : Eq (beq n m) false → Not (Eq n m) := by {
  intro h
  rcases rat_destruct n with ⟨a, b, b_neq, hn⟩
  rcases rat_destruct m with ⟨c, d, d_neq, hm⟩
  rw [hn.symm, hm.symm]
  rw [hn.symm, hm.symm, beq_nat] at h
  have h' := of_decide_eq_false h
  intro h2
  have h2' := rel_rat_int h2
  contradiction
}

def decEq (n m : MyRat) : Decidable (Eq n m) :=
  match h:beq n m with
  | true  => isTrue (eq_of_beq_eq_true h)
  | false  => isFalse (ne_of_beq_eq_false h)

@[inline] instance : DecidableEq MyRat := MyRat.decEq
