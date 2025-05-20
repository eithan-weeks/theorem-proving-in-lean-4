namespace AAAAAA
  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ y : α, p y
  :=
    fun h : ∀ x : α, p x ∧ q x =>
    fun y : α =>
    show p y from (h y).left
end AAAAAA

namespace AAAAAA.mine
  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x : α, p x ∧ q x) → (∀ y : α, p y)
  :=
    λ x_hpx_qx ↦
      λ y ↦ (x_hpx_qx y).left

  example : ∀ {α : Type} {p q : α → Prop},
    ∀ {x : α}, p x ∧ q x → p x
  :=
    λ hpx_qx ↦ hpx_qx.left

  example : ∀ {α : Type} {p q : α → Prop} {x : α}, p x ∧ q x → p x :=
    λ hpx_qx ↦ hpx_qx.left
end AAAAAA.mine

namespace AAABBB
  example (α : Type) (p q : α → Prop) :
    (∀ x : α, p x ∧ q x) → ∀ x : α, p x
  :=
    fun h : ∀ x : α, p x ∧ q x =>
    fun z : α =>
    show p z from And.left (h z)
end AAABBB

namespace AAABBB.mine
  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x : α, p x ∧ q x) → (∀ x : α, p x)
  :=
    λ x_hpx_qx ↦
      λ x ↦ (x_hpx_qx x).left
end AAABBB.mine

namespace AAACCC
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ x y z, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r a b c
  #check trans_r a b c hab
  #check trans_r a b c hab hbc
end AAACCC

namespace AAACCC.mine
  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x, p x ∧ q x) → (∀ x, p x)
  :=
    λ x_hpx_qx ↦
      λ x ↦ (x_hpx_qx x).left
end AAACCC.mine

namespace AAADDD
  variable (α : Type) (r : α → α → Prop)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  variable (a b c : α)
  variable (hab : r a b) (hbc : r b c)

  #check trans_r
  #check trans_r hab
  #check trans_r hab hbc
end AAADDD

namespace AAADDD.mine
  variable (trans_r : ∀ (α : Type) (r : α → α → Prop),
    ∀ {x y z}, r x y → r y z → r x z)

  #check trans_r
  -- #print trans_r

  -- variable (a b c : α)
  -- variable (hab : r a b) (hbc : r b c)

  variable (α : Type)
  variable (a b c : α)

  #check a
  -- #print a

  #check False
  #check False.elim
  #check (False.elim)

  variable (f : False)
  #check f
  #check False.elim f
  #check @False.elim Nat f

  example : ∀ {p : Prop}, p ∧ ¬p :=
    False.elim f

  variable (f1 : False)
  axiom f2 : False

  example : ∀ {p : Prop}, p ∧ ¬p :=
    False.elim f1

  -- theorem ex1 : ∀ {p : Prop}, p ∧ ¬p :=
  --   False.elim f1

  theorem ex2 : ∀ {p : Prop}, p ∧ ¬p :=
    False.elim f2
end AAADDD.mine

namespace AAAEEE
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd
end AAAEEE

namespace AAAEEE.mine_v1
  variable (α : Type) (r : α → α → Prop)

  variable (refl_r : ∀ x, r x x)
  variable (symm_r : ∀ {x y}, r x y → r y x)
  variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

  example : ∀ {a b c d : α},
    r a b → r c b → r c d → r a d
  :=
    λ hab hcb hcd ↦ trans_r (trans_r hab (symm_r hcb)) hcd
end AAAEEE.mine_v1

namespace AAAEEE.mine_v2
  variable (r : ∀ {α : Type}, α → α → Prop)

  variable (refl_r : ∀ {α : Type} (x : α), r x x)
  variable (symm_r : ∀ {α : Type} {x y : α}, r x y → r y x)
  variable (trans_r : ∀ {α : Type} {x y z : α}, r x y → r y z → r x z)

  example : ∀ {α : Type} {a b c d : α},
    r a b → r c b → r c d → r a d
  :=
    λ hab hcb hcd ↦ trans_r (trans_r hab (symm_r hcb)) hcd
end AAAEEE.mine_v2

namespace AAAEEE.mine_v3
  #check Type
  #check Type → Type 1
  #check Prop
  #check Prop → Type
  #check Type → Prop
  #check True
  #check True → Prop
  #check Prop → True
  #check Type → True
end AAAEEE.mine_v3

namespace AAAFFF
  #check Eq.refl
  #check Eq.symm
  #check Eq.trans
end AAAFFF

namespace AAAGGG
  universe u

  #check @Eq.refl.{u}
  #check @Eq.symm.{u}
  #check @Eq.trans.{u}
end AAAGGG

namespace AAAGGG.mine
  universe u

  #check Eq
  #check @Eq.{u}

  variable (ex1 : ∀ {α : Sort u} (a : α), a = a)
  variable (ex2 : ∀ {α : Sort u}, (a : α) → a = a)
  variable (ex3 : {α : Sort u} → (a : α) → a = a)
  variable (ex4 : {α : Type} → (a : α) → a = a)
  variable (ex5 : (α : Type) → (a : α) → a = a)
  variable (ex6 : (α : Type) → (a : α) → α)
  variable (ex7 : (α : Type) → (a : α) → Prop)

  #check @ex1
  #check @ex2
  #check @ex3
  #check @ex4
  #check @ex5
  #check @ex6
  #check @ex7
end AAAGGG.mine

namespace AAAHHH
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)

  example : a = d :=
    Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
end AAAHHH

namespace AAAIII
  variable (α : Type) (a b c d : α)
  variable (hab : a = b) (hcb : c = b) (hcd : c = d)

  example : a = d := (hab.trans hcb.symm).trans hcd
end AAAIII

namespace AAAJJJ
  variable (α β : Type)

  example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
  example (a : α) (b : β) : (a, b).1 = a := Eq.refl _
  example : 2 + 3 = 5 := Eq.refl _
end AAAJJJ

namespace AAAJJJ.mine
  variable (α β : Type)

  variable (f : α → β)
  #check f
  #check λ x ↦ f x

  variable (a : α) (b : β)
  #check a
  #check b
  #check a = a

  #check f a
  #check (λ x ↦ f x) a

  universe u
  #check @Eq.refl.{u}
end AAAJJJ.mine

namespace AAAKKK
  variable (α β : Type)

  example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl
  example (a : α) (b : β) : (a, b).1 = a := rfl
  example : 2 + 3 = 5 := rfl
end AAAKKK

namespace AAAKKK.mine
  universe u
  #check @Eq.refl.{u}
  #check rfl
end AAAKKK.mine

namespace AAALLL
  example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b :=
    Eq.subst h1 h2

  example (α : Type) (a b : α) (p : α → Prop)
      (h1 : a = b) (h2 : p a) : p b :=
    h1 ▸ h2
end AAALLL

namespace AAALLL.mine
  variable (α : Type)
  variable (a b : α)
  variable (p : α → Prop)
  variable (h1 : a = b)
  variable (h2 : p a)

  #check p
  #check p a
  #check p b
  #check h1
  #check h2

  #check Eq.subst
  #check Eq.subst h1 h2

  variable (h3 : Prop)
  -- #check Eq.subst h1 h3
end AAALLL.mine

namespace AAAMMM
  variable (α : Type)
  variable (a b : α)
  variable (f g : α → Nat)
  variable (h₁ : a = b)
  variable (h₂ : f = g)

  example : f a = f b := congrArg f h₁
  example : f a = g a := congrFun h₂ a
  example : f a = g b := congr h₂ h₁
end AAAMMM

namespace AAANNN
  variable (a b c : Nat)

  example : a + 0 = a := Nat.add_zero a
  example : 0 + a = a := Nat.zero_add a
  example : a * 1 = a := Nat.mul_one a
  example : 1 * a = a := Nat.one_mul a
  example : a + b = b + a := Nat.add_comm a b
  example : a + b + c = a + (b + c) := Nat.add_assoc a b c
  example : a * b = b * a := Nat.mul_comm a b
  example : a * b * c = a * (b * c) := Nat.mul_assoc a b c
  example : a * (b + c) = a * b + a * c := Nat.mul_add a b c
  example : a * (b + c) = a * b + a * c := Nat.left_distrib a b c
  example : (a + b) * c = a * c + b * c := Nat.add_mul a b c
  example : (a + b) * c = a * c + b * c := Nat.right_distrib a b c
end AAANNN

namespace AAANNN.mine
  variable (a b c : Nat)

  #check a = b
  #check a + b

  #check Nat.add_zero
  #check Nat.zero_add
end AAANNN.mine

namespace AAAOOO
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    have h1 : (x + y) * (x + y) = (x + y) * x + (x + y) * y :=
      Nat.mul_add (x + y) x y
    have h2 : (x + y) * (x + y) = x * x + y * x + (x * y + y * y) :=
      (Nat.add_mul x y x) ▸ (Nat.add_mul x y y) ▸ h1
    h2.trans (Nat.add_assoc (x * x + y * x) (x * y) (y * y)).symm
end AAAOOO

namespace AAAOOO.mine
  example : ∀ (x y : Nat),
    (x + y) * (x + y) = x * x + y * x + x * y + y * y
  :=
    λ x y ↦
      have h1 := Nat.mul_add (x + y) x y
      have h2 := Nat.add_mul x y x
      have h3 := Nat.add_mul x y y
      have h4 := h2 ▸ h3 ▸ h1
      have h5 := Nat.add_assoc (x * x + y * x) (x * y) (y * y)
      have h6 := Eq.symm h5
      Eq.trans h4 h6

  example : ∀ (x y : Nat),
    (x + y) * (x + y) = x * x + y * x + x * y + y * y
  :=
    λ x y ↦
      Eq.trans
        (
          (Nat.add_mul x y x) ▸
          (Nat.add_mul x y y) ▸
          (Nat.mul_add (x + y) x y)
        )
        (Eq.symm
          (Nat.add_assoc (x * x + y * x) (x * y) (y * y))
        )

  universe u
  #check @Eq.subst.{u}
end AAAOOO.mine

namespace AAAPPP
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  -- theorem T : a = e :=
  example : a = e :=
    calc
      a = b     := h1
      _ = c + 1 := h2
      _ = d + 1 := congrArg Nat.succ h3
      _ = 1 + d := Nat.add_comm d 1
      _ = e     := Eq.symm h4
end AAAPPP

namespace AAAPPP.mine
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  example : a = e :=
    have e1 : a = b     := h1
    have e2 : _ = c + 1 := h2
    have e3 : _ = d + 1 := congrArg Nat.succ h3
    have e4 : _ = 1 + d := Nat.add_comm d 1
    have e5 : _ = e     := Eq.symm h4
    (((e1.trans e2).trans e3).trans e4).trans e5

  example : a = e :=
    have e1 := h1
    have e2 := h2
    have e3 := congrArg Nat.succ h3
    have e4 := Nat.add_comm d 1
    have e5 := Eq.symm h4
    (((e1.trans e2).trans e3).trans e4).trans e5

  universe u v
  #check @Eq.subst.{u}
  #check @congrArg.{u, v}
  #check @congrFun.{u, v}
  #check @congr.{u, v}

  #check h3
  #check @Nat.succ
  #check congrArg Nat.succ h3
  -- #check congrArg Nat.succ (a = b)
  #check congrArg (λ x ↦ x + 1) h3
  #check Nat.add_comm d 1
  #check congrArg (λ x ↦ x + 1) (Eq.refl a)

  #check calc sorry
end AAAPPP.mine

namespace AAAQQQ
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  -- theorem T : a = e :=
  example : a = e :=
    calc
      a = b     := by rw [h1]
      _ = c + 1 := by rw [h2]
      _ = d + 1 := by rw [h3]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e     := by rw [h4]
end AAAQQQ

namespace AAARRR
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  -- theorem T : a = e :=
  example : a = e :=
    calc
      a = d + 1 := by rw [h1, h2, h3]
      _ = 1 + d := by rw [Nat.add_comm]
      _ = e     := by rw [h4]
end AAARRR

namespace AAASSS
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  -- theorem T : a = e :=
  example : a = e :=
    by rw [h1, h2, h3, Nat.add_comm, h4]
end AAASSS

namespace AAATTT
  variable (a b c d e : Nat)
  variable (h1 : a = b)
  variable (h2 : b = c + 1)
  variable (h3 : c = d)
  variable (h4 : e = 1 + d)

  -- theorem T : a = e :=
  example : a = e :=
    by simp [h1, h2, h3, Nat.add_comm, h4]
end AAATTT

namespace AAAUUU
  example (a b c d : Nat) (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
    calc
      a = b     := h1
      _ < b + 1 := Nat.lt_succ_self b
      _ ≤ c + 1 := Nat.succ_le_succ h2
      _ < d     := h3
end AAAUUU

namespace AAAUUU.mine
  #check @Nat.succ_le_succ

  example : ∀ (a b c d : Nat),
      a = b →
      b ≤ c →
      c + 1 < d →
      a < d
  :=
    λ a b c d h1 h2 h3 ↦
      have e1 : a = b     := h1
      have e2 : _ < b + 1 := Nat.lt_succ_self b
      have e3 : _ ≤ c + 1 := Nat.succ_le_succ h2
      have e4 : _ < d     := h3
      -- ((e1.trans e2).trans e3).trans e4
      calc
        _ = _ := e1
        _ < _ := e2
        _ ≤ _ := e3
        _ < _ := e4
end AAAUUU.mine

namespace AAAVVV
  def divides (x y : Nat) : Prop :=
    ∃ k, k * x = y

  def divides_trans {x y z} (h₁ : divides x y) (h₂ : divides y z) : divides x z :=
    let ⟨k₁, d₁⟩ := h₁
    let ⟨k₂, d₂⟩ := h₂
    ⟨k₁ * k₂, by rw [Nat.mul_comm k₁ k₂, Nat.mul_assoc, d₁, d₂]⟩

  def divides_mul (x : Nat) (k : Nat) : divides x (k * x) :=
    ⟨k, rfl⟩

  instance : Trans divides divides divides where
    trans := divides_trans

  example {x y z} (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
    calc
      divides x y       := h₁
      _ = z             := h₂
      divides _ (2 * z) := divides_mul ..

  infix:50 " | " => divides

  example {x y z} (h₁ : divides x y) (h₂ : y = z) : divides x (2 * z) :=
    calc
      x | y     := h₁
      _ = z     := h₂
      _ | 2 * z := divides_mul ..
end AAAVVV

namespace AAAVVV.mine
  universe u v w x y z
  #check @Trans.{u, v, w, x, y, z}
end AAAVVV.mine

namespace AAAWWW
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc
      (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y               := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y)           := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y             := by rw [←Nat.add_assoc]
end AAAWWW

namespace AAAXXX
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    calc (x + y) * (x + y)
      _ = (x + y) * x + (x + y) * y       := by rw [Nat.mul_add]
      _ = x * x + y * x + (x + y) * y     := by rw [Nat.add_mul]
      _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
      _ = x * x + y * x + x * y + y * y   := by rw [←Nat.add_assoc]
end AAAXXX

namespace AAAYYY
  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, ←Nat.add_assoc]

  example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
    by simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc]
end AAAYYY

namespace AAAYYY.mine
  universe u
  #check @Exists.{u}

  variable (α : Type)
  variable (p : α → Prop)

  #check ∀ x : α, p x
  #check ∃ x : α, p x

  variable (f1 : ∀ x : α, p x)
  variable (f2 : ∃ x : α, p x)

  #check f1
  #check f2

  variable (β : α → Type)

  #check (a : α) → β a

  variable (g1 : (a : α) → β a)

  #check g1

  variable (x : α)
  #check p x

  #check (x : α) → p x          -- transformation from ∀ x : α, p x
  #check Exists (λ x : α ↦ p x) -- transformation from ∃ x : α, p x

  variable (i1 : (x : α) → p x)
  variable (i2 : Exists (λ x : α ↦ p x))

  #check i1
  #check i2
end AAAYYY.mine

namespace AAAZZZ
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    Exists.intro 1 h

  example (x : Nat) (h : x > 0) : ∃ y, y < x :=
    Exists.intro 0 h

  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    Exists.intro y (And.intro hxy hyz)

  #check @Exists.intro
end AAAZZZ

namespace AAAZZZ.mine
  #check Nat.zero_lt_succ

  universe u
  #check @Exists.intro.{u}

  #check Exists (λ x : Nat ↦ x > 0) -- transformation from ∃ x : Nat, x > 0

  variable (x : Nat)
  #check x > 0
  #check @Nat.zero_lt_succ
  #check Nat.zero_lt_succ 0
  -- #check (Nat.zero_lt_succ 0 : x > 0)
  #check (Nat.zero_lt_succ 0 : 1 > 0)

  variable (h1 : 1 > 0)
  variable (h2 : x > 0)
  #check h1
  #check h2
end AAAZZZ.mine

namespace BBBAAA
  example : ∃ x : Nat, x > 0 :=
    have h : 1 > 0 := Nat.zero_lt_succ 0
    ⟨1, h⟩

  example (x : Nat) (h : x > 0) : ∃ y, y < x :=
    ⟨0, h⟩

  example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
    ⟨y, hxy, hyz⟩
end BBBAAA

namespace BBBAAA.mine
  example :
    ∀ {x : Nat},
    x > 0 →
    ∃ y, y < x
  :=
    λ h ↦ ⟨0, h⟩

  example :
    ∀ {x y z : Nat},
    x < y →
    y < z →
    ∃ w, x < w ∧ w < z
  :=
    λ {_ y _} hxy hyz ↦ ⟨y, ⟨hxy, hyz⟩⟩

  universe u
  #check @Exists.intro.{u}
end BBBAAA.mine

namespace BBBBBB
  variable (g : Nat → Nat → Nat)
  -- variable (hg : g 0 0 = 0)

  theorem gex1 {hg : g 0 0 = 0} : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 {hg : g 0 0 = 0} : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 {hg : g 0 0 = 0} : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 {hg : g 0 0 = 0} : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.explicit true
  #print gex1
  #print gex2
  #print gex3
  #print gex4
end BBBBBB

namespace BBBCCC
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    Exists.elim h
      (fun w =>
       fun hw : p w ∧ q w =>
       show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)
end BBBCCC

namespace BBBCCC.mine
  universe u
  #check @Exists.elim.{u}

  example :
    ∀ {α : Type} {p q : α → Prop},
    (∃ x, p x ∧ q x) →
    (∃ x, q x ∧ p x)
  :=
    λ h ↦ Exists.elim h (λ w hw ↦ ⟨w, ⟨hw.right, hw.left⟩⟩)
end BBBCCC.mine

namespace BBBDDD
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩
end BBBDDD

namespace BBBEEE
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩
end BBBEEE

namespace BBBFFF
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    match h with
    | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
end BBBFFF

namespace BBBGGG
  variable (α : Type) (p q : α → Prop)

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
    let ⟨w, hpw, hqw⟩ := h
    ⟨w, hqw, hpw⟩
end BBBGGG

namespace BBBHHH
  variable (α : Type) (p q : α → Prop)

  example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
    fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩
end BBBHHH

namespace BBBHHH.mine
  example : ∀ {α : Prop} {p q : α → Prop},
    (∃ x, p x ∧ q x) → (∃ x, q x ∧ p x)
  :=
    λ ⟨w, hpw, hqw⟩ ↦ ⟨w, hqw, hpw⟩
end BBBHHH.mine

namespace BBBIII
  def is_even (a : Nat) := ∃ b, a = 2 * b

  theorem even_plus_even {a b} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    Exists.elim h1 (fun w1 (hw1 : a = 2 * w1) =>
    Exists.elim h2 (fun w2 (hw2 : b = 2 * w2) =>
      Exists.intro (w1 + w2)
        (calc a + b
          _ = 2 * w1 + 2 * w2 := by rw [hw1, hw2]
          _ = 2 * (w1 + w2)   := by rw [Nat.mul_add])))
end BBBIII

namespace BBBIII.mine
  def is_even : Nat → Prop := λ x ↦ ∃ y, x = 2 * y

  theorem even_plus_even :
    ∀ {a b}, is_even a → is_even b → is_even (a + b)
  := λ {a b} ha hb ↦
    ha.elim (λ u hu ↦
    hb.elim (λ v hv ↦
      ⟨u + v, (calc a + b
        _ = 2 * u + 2 * v := by rw [hu, hv]
        _ = 2 * (u + v)   := by rw [Nat.mul_add]
      )⟩
    ))

  example :
    ∀ {a b}, is_even a → is_even b → is_even (a + b)
  := λ {a b} ha hb ↦
    ha.elim (λ u hu ↦
    hb.elim (λ v hv ↦
      ⟨u + v, by rw [hu, hv, Nat.mul_add]⟩
    ))
end BBBIII.mine

namespace BBBJJJ
  def is_even (a : Nat) := ∃ b, a = 2 * b

  theorem even_plus_even {a b} (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
    match h1, h2 with
    | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩
end BBBJJJ

namespace BBBKKK
  open Classical
  variable (α)
  variable (p : α → Prop)

  example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
    byContradiction
      (fun h1 : ¬ ∃ x, p x =>
        have h2 : ∀ x, ¬ p x :=
          fun x =>
          fun h3 : p x =>
          have h4 : ∃ x, p x := ⟨x, h3⟩
          show False from h1 h4
        show False from h h2)
end BBBKKK

namespace BBBKKK.mine
  example :
    ∀ {α} {p : α → Prop},
    (¬ ∀ x, ¬ p x) →
    (∃ x, p x)
  :=
    λ {_ p} hn ↦ Classical.byContradiction (λ rn ↦
      have h := λ x hpx ↦
        have r : ∃ x, p x := ⟨x, hpx⟩
        rn r
      hn h
    )
end BBBKKK.mine

namespace BBBLLL
  -- open Classical

  -- variable (α : Type) (p q : α → Prop)
  -- variable (r : Prop)

  -- example : (∃ x : α, r) → r := sorry
  -- example (a : α) : r → (∃ x : α, r) := sorry
  -- example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
  -- example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

  -- example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
  -- example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
  -- example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  -- example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  -- example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  -- example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  -- example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end BBBLLL

namespace BBBMMM
  set_option linter.unusedVariables false

  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (a : α)
  variable (r : Prop)

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    Iff.intro
      (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
        Or.elim h1
          (fun hpa : p a => Or.inl ⟨a, hpa⟩)
          (fun hqa : q a => Or.inr ⟨a, hqa⟩))
      (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
        Or.elim h
          (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
          (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    Iff.intro
      (fun ⟨b, (hb : p b → r)⟩ =>
       fun h2 : ∀ x, p x =>
       show r from hb (h2 b))
      (fun h1 : (∀ x, p x) → r =>
       show ∃ x, p x → r from
         byCases
           (fun hap : ∀ x, p x => ⟨a, λ h' => h1 hap⟩)
           (fun hnap : ¬ ∀ x, p x =>
            byContradiction
              (fun hnex : ¬ ∃ x, p x → r =>
                have hap : ∀ x, p x :=
                  fun x =>
                  byContradiction
                    (fun hnp : ¬ p x =>
                      have hex : ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                      show False from hnex hex)
                show False from hnap hap)))
end BBBMMM

namespace BBBNNN
  variable (f : Nat → Nat)
  variable (h : ∀ x : Nat, f x ≤ f (x + 1))

  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
    show f 0 ≤ f 3 from Nat.le_trans this (h 2)
end BBBNNN

namespace BBBOOO
  variable (f : Nat → Nat)
  variable (h : ∀ x : Nat, f x ≤ f (x + 1))

  example : f 0 ≤ f 3 :=
    have : f 0 ≤ f 1 := h 0
    have : f 0 ≤ f 2 := Nat.le_trans (by assumption) (h 1)
    show f 0 ≤ f 3 from Nat.le_trans (by assumption) (h 2)
end BBBOOO

namespace BBBPPP
  notation "‹" p "›" => show p by assumption
end BBBPPP

namespace BBBQQQ
  -- variable (f : Nat → Nat)
  -- variable (h : ∀ x : Nat, f x ≤ f (x + 1))

  -- example : f 0 ≥ f 1 → f 1 ≥ f 2 → f 0 = f 2 :=
  --   fun _ : f 0 ≥ f 1 =>
  --   fun _ : f 1 ≥ f 2 =>
  --   have : f 0 ≥ f 2 := Nat.le_trans ‹f 1 ≥ f 2› ‹f 0 ≥ f 1›
  --   have : f 0 ≤ f 2 := Nat.le_trans (h 0) (h 1)
  --   show f 0 = f 2 from Nat.le_antisymm this ‹f 0 ≥ f 2›
end BBBQQQ

namespace BBBQQQ.mine
  #check Nat.le_antisymm
end BBBQQQ.mine

namespace BBBRRR
  -- example (n : Nat) : Nat := ‹Nat›
end BBBRRR

namespace BBBSSS
  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x)
  :=
    ⟨
      λ xpxqx ↦ ⟨λ _ ↦ (xpxqx _).left, λ _ ↦ (xpxqx _).right⟩,
      λ xpx_xqx x ↦ ⟨xpx_xqx.left x, xpx_xqx.right x⟩
    ⟩

  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x)
  :=
    λ xpxqx xpx x ↦ xpxqx x (xpx x)

  example : ∀ {α : Type} {p q : α → Prop},
    (∀ x, p x) ∨ (∀ x, q x) → (∀ x, p x ∨ q x)
  :=
    λ xpx_xqx x ↦ xpx_xqx.elim
      (λ xpx ↦ Or.inl (xpx x))
      (λ xqx ↦ Or.inr (xqx x))

  /- Understand why the reverse implication is not derivable in the last example. -/
end BBBSSS

namespace BBBTTT
  example :
    ∀ {α : Type} {r : Prop},
    α → ((∀ _ : α, r) ↔ r)
  :=
    λ x ↦ ⟨
      λ xr ↦ xr x,
      λ hr _ ↦ hr
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r
  :=
    λ {_ _ r} ↦ ⟨
      λ xpxr ↦ (Classical.em r).elim
        (λ hr ↦ Or.inr hr)
        (λ hnr ↦ Or.inl λ x ↦ (xpxr x).elim
          (λ hpx ↦ hpx)
          (λ hr ↦ absurd hr hnr)),
      λ xpx_r x ↦ xpx_r.elim
        (λ xpx ↦ Or.inl (xpx x))
        (λ hr ↦ Or.inr hr)
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    (∀ x, r → p x) ↔ (r → ∀ x, p x)
  :=
    ⟨
      λ xrpx hr x ↦ xrpx x hr,
      λ rxpx x hr ↦ rxpx hr x
    ⟩
end BBBTTT

namespace BBBTTT.mine
  example :
    ∀ {α : Type} {r : Prop},
    r → (∀ _ : α, r)
  :=
    λ hr ↦ (λ _ ↦ hr)

  example :
    ∀ {p q : Prop},
    (p → q → p) ∨ ¬(p → q → p)
  :=
    Or.inl λ hp _ ↦ hp

  example : ∀ {p : Prop}, p ↔ ¬¬p :=
    ⟨
      λ hp ↦ (λ hnp ↦ absurd hp hnp),
      λ hnnp ↦ Classical.byContradiction λ hnp ↦ absurd hnp hnnp
    ⟩

  -- Derive exclude in the middle from double negation
  -- example : ∀ {p : Prop}, (p ∨ ¬p) :=
  --   sorry
end BBBTTT.mine

namespace BBBUUU
  example :
    ∀ {men : Type} {barber : men} {shaves : men → men → Prop},
    (∀ x : men, shaves barber x ↔ ¬ shaves x x) → False
  :=
    λ {_ barber _} sbx_nsxx ↦
      have sbb_nsbb := sbx_nsxx barber
      have nsbb := λ sbb ↦ sbb_nsbb.mp sbb sbb
      have sbb := sbb_nsbb.mpr nsbb
      absurd sbb nsbb
end BBBUUU

namespace BBBUUU.mine
  example : ∀ {p : Prop}, ¬(p ↔ ¬p) :=
    λ p_np ↦
      have hnp := λ hp ↦ p_np.mp hp hp
      have hp := p_np.mpr hnp
      absurd hp hnp
end BBBUUU.mine

namespace BBBVVV
  def even : Nat → Prop :=
    λ n ↦
      2 | n

  def prime : Nat → Prop :=
    λ n ↦
      ¬ ∃ m, m > 1 ∧ m < n ∧ m | n

  def infinitely_many_primes : Prop :=
    ∀ n, ∃ p,
      p > n ∧ prime p

  def Fermat_prime : Nat → Prop :=
    λ n ↦
      prime n ∧ ∃ k : Nat, 2 ^ (2 ^ k) + 1 = n

  def infinitely_many_Fermat_primes : Prop :=
    ∀ n, ∃ p,
      p > n ∧ Fermat_prime p

  def goldbach_conjecture : Prop :=
    ∀ n, n > 2 → ∃ p q,
      prime p ∧ prime q ∧ n = p + q

  def Goldbach's_weak_conjecture : Prop :=
    ∀ n, ¬ even n ∧ n > 5 → ∃ p q r,
      prime p ∧ prime q ∧ prime r ∧ n = p + q + r

  def Fermat's_last_theorem : Prop :=
    ∀ n, n > 2 → ¬ ∃ a b c,
      a ^ n + b ^ n = c ^ n ∧ a > 0 ∧ b > 0 ∧ c > 0
end BBBVVV

namespace BBBWWW
  example :
    ∀ {α : Type} {r : Prop},
    (∃ _ : α, r) → r
  :=
    λ xr ↦ xr.elim λ _ hr ↦ hr

  example :
    ∀ {α : Type} {r : Prop},
    α → r → (∃ _ : α, r)
  :=
    λ hα hr ↦ ⟨hα, hr⟩

  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r
  :=
    ⟨
      λ xpxr ↦ xpxr.elim λ x hpxr ↦ ⟨⟨x, hpxr.left⟩, hpxr.right⟩,
      λ xpx_r ↦ xpx_r.left.elim λ x hpx ↦ ⟨x, ⟨hpx, xpx_r.right⟩⟩
    ⟩

  example :
    ∀ {α : Type} {p q : α → Prop},
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x)
  :=
    ⟨
      λ xpxqx ↦ xpxqx.elim λ x hpxqx ↦ hpxqx.elim
        (λ hpx ↦ Or.inl ⟨x, hpx⟩)
        (λ hqx ↦ Or.inr ⟨x, hqx⟩),
      λ xpx_xqx ↦ xpx_xqx.elim
        (λ xpx ↦ xpx.elim λ x hpx ↦ ⟨x, Or.inl hpx⟩)
        (λ xqx ↦ xqx.elim λ x hqx ↦ ⟨x, Or.inr hqx⟩)
    ⟩


  example :
    ∀ {α : Type} {p : α → Prop},
    (∀ x, p x) ↔ ¬ (∃ x, ¬ p x)
  :=
    ⟨
      λ xpx xnpx ↦xnpx.elim λ x hnpx ↦ absurd (xpx x) hnpx,
      λ nxnpx x ↦ Classical.byContradiction λ hnpx ↦
        absurd ⟨x, hnpx⟩ nxnpx
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop},
    (∃ x, p x) ↔ ¬ (∀ x, ¬ p x)
  :=
    ⟨
      λ xpx xnpx ↦ xpx.elim λ x hpx ↦ absurd hpx (xnpx x),
      λ nxnpx ↦ Classical.byContradiction λ nxpx ↦
        absurd (λ x hpx ↦ absurd ⟨x, hpx⟩ nxpx) nxnpx
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop},
    (¬ ∃ x, p x) ↔ (∀ x, ¬ p x)
  :=
    ⟨
      λ nxpx x hpx ↦ absurd ⟨x, hpx⟩ nxpx,
      λ xnpx xpx ↦ xpx.elim λ x hpx ↦ absurd hpx (xnpx x)
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop},
    (¬ ∀ x, p x) ↔ (∃ x, ¬ p x)
  :=
    ⟨
      λ nxpx ↦ Classical.byContradiction λ nxnpx ↦
        absurd
          (λ x ↦ Classical.byContradiction λ hnpx ↦
            absurd ⟨x, hnpx⟩ nxnpx)
          nxpx,
      λ xnpx xpx ↦ xnpx.elim λ x hnpx ↦ absurd (xpx x) hnpx
    ⟩


  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    (∀ x, p x → r) ↔ (∃ x, p x) → r
  :=
    ⟨
      λ xpxr xpx ↦ xpx.elim λ x hpx ↦ xpxr x hpx,
      λ xpx_r x hpx ↦ xpx_r ⟨x, hpx⟩
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    α → ((∃ x, p x → r) ↔ (∀ x, p x) → r)
   :=
    λ {_ p _} hα ↦ ⟨
      λ xpxr xpx ↦ xpxr.elim λ x pxr ↦ pxr (xpx x),
      λ xpx_r ↦ (Classical.em (∀ x, p x)).elim
        (λ xpx ↦ ⟨hα, λ _ ↦ xpx_r xpx⟩)
        (λ nxpx ↦
          have xnpx : ∃ x, ¬p x :=
            Classical.byContradiction λ nxnpx ↦
              absurd
                (λ x ↦ Classical.byContradiction λ hnp ↦
                  absurd ⟨x, hnp⟩ nxnpx)
                nxpx
          xnpx.elim λ x hnpx ↦ ⟨x, λ hpx ↦ absurd hpx hnpx⟩)
    ⟩

  example :
    ∀ {α : Type} {p : α → Prop} {r : Prop},
    α → ((∃ x, r → p x) ↔ (r → ∃ x, p x))
  :=
    λ {_ _ r} hα ↦ ⟨
      λ xrpx hr ↦ xrpx.elim λ x rpx ↦ ⟨x, rpx hr⟩,
      λ r_xpx ↦ (Classical.em r).elim
        (λ hr ↦ (r_xpx hr).elim λ x hpx ↦ ⟨x, λ _ ↦ hpx⟩)
        (λ hnr ↦ ⟨hα, λ hr ↦ absurd hr hnr⟩)
    ⟩
end BBBWWW
