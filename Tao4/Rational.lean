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

def inv_fn (a: myrat) (a_neq : a.n ≠ 0) : MyRat := (a.d // a.n) a_neq

private theorem inv_respects (a a' : myrat) (ha: a.n ≠ 0) (ha': a'.n ≠ 0) (haa': a ~ a') : inv_fn a ha = inv_fn a' ha' := by {
  unfold rel_rat at haa'
  apply rel_int_rat
  rw [mul_comm, haa'.symm]
  ring
}

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

-- I can prove it just fine using this structure
structure temp_rat where
  mk ::
  r: myrat
  n_neq: r.n ≠ 0

def rel_temp_rat (a: temp_rat) (b: temp_rat) : Prop := a.r ~ b.r

private theorem is_equivalence_temp : Equivalence rel_temp_rat where
  refl := fun x => rel_rat_refl x.r
  symm := fun a => rel_rat_symm a
  trans := fun a1 a2 => rel_rat_trans a1 a2

instance tempSetoid : Setoid (temp_rat) where
  r     := rel_temp_rat
  iseqv := is_equivalence_temp

def TempRat := Quotient tempSetoid

def temp_mk (n d : MyInt) (n_neq : n ≠ 0) (d_neq : d ≠ 0) : TempRat := Quotient.mk' (temp_rat.mk (myrat.mk n d d_neq) n_neq)

-- as seen here
def inv_temp (a : TempRat) : MyRat :=
  Quot.liftOn a (fun x => inv_fn x.r x.n_neq) (by {
    intro a a' haa'
    exact inv_respects a.r a'.r a.n_neq a'.n_neq haa'
  })

-- but I can't find a way to do it with MyRat. we can infer that the numerator is non zero
-- from a ≠ 0 from neq_num_neq_zero, but I'm really not sure on how to apply that here,
-- as I can't pass the inequality to the liftOn function.
-- for now, we can only do sorry, I don't know how to do it as mentioned above
/-
  after looking around, other people seem to avoid this problem by doing the following:
  · define the inverse function for a zero casem this is what the stdlib and some other people do and makes it more ergonomic as it doesn't need to carry the ≠0 everywhere
  · not using Quot and using a ≃ equivalence everywhere, this is what lean4-axiomatic does and from this it's naturally possible to do everything but that doesn't seem practical and would change pretty much everything (rw, etc)

  I really like the second solution, but for now I think I'll hold off from it and just do the cases
-/
def inv (a: MyRat) (ha: a ≠ 0) : MyRat :=
  Quot.liftOn a (fun x => inv_fn x sorry) (by {
    intro b b' hbb'
    exact inv_respects b b' sorry sorry hbb'
  })

infix:160 " ⁻¹ " => inv

theorem inv_int {a b: MyInt} {b_neq : b ≠ 0} {a_neq : a ≠ 0} : ((a // b) b_neq) ⁻¹ (neq_num_neq_zero' b_neq a_neq) = (b // a) a_neq := by {
  apply rel_int_rat
  simp only
}

theorem cancel (a : MyRat) (ha: a ≠ 0): a*(a ⁻¹ ha) = 1 := by {
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

def div (a : MyRat) (b : MyRat) {b_neq : b ≠0 }: MyRat :=
  a * b ⁻¹ b_neq

infixl:70 " / "   => div

def pos_rat (a : MyRat) := ∃ (x y : MyInt) (y_pos: y ≠ 0), x ≥ 0 ∧ y > 0 ∧ a = (x // y) (y_pos)
def neg_rat (a : MyRat) := ∃ (b : MyRat), pos_rat b ∧ a = -b

theorem is_pos (n m: MyInt) (m_neq: m ≠ 0) (ha: n > 0) (hb: m > 0) : pos_rat ((n // m) m_neq) := by {
  unfold pos_rat;
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

theorem trichotomy (a : MyRat) : (pos_rat a) ∨ (a = 0) ∨ (neg_rat a)  := by {
  rcases rat_destruct a with ⟨n, m, m_neq, h1⟩
  have m_neg_neq : (-1: MyInt) ≠ 0 := by {
    intro h
    rw [MyInt.one_eq, MyInt.zero_eq] at h
    have a := MyInt.rel_int_nat h
    simp only at a
    rw [mynat.zero_add, mynat.zero_add, mynat.one_eq_succ_zero] at a
    exact mynat.succ_ne_zero 0 a.symm
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
  unfold neg_rat;

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
  unfold neg_rat;
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

def lt (x y : MyRat) : Prop := neg_rat (x - y)
def le (x y : MyRat) : Prop := lt x y ∨ x = y

instance : LE MyRat where le := le
instance : LT MyRat where lt := lt
