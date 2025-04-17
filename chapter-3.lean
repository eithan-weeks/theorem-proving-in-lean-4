namespace AAAAAA
  def Implies (p q : Prop) : Prop := p → q

  #check And
  #check Or
  #check Not
  #check Implies

  variable (p q r : Prop)
  #check And p q
  #check Or (And p q) r
  #check Implies (And p q) (And q p)
end AAAAAA

namespace AAABBB
  def Implies (p q : Prop) : Prop := p → q
  structure Proof (p : Prop) : Type where
    proof : p

  #check Proof
  #check (Proof)

  axiom and_comm (p q : Prop) : Proof (Implies (And p q) (And q p))

  variable (p q : Prop)
  #check and_comm p q
end AAABBB

namespace AAACCC
  def Implies (p q : Prop) : Prop := p → q
  structure Proof (p : Prop) : Type where
    proof : p

  axiom modus_ponens : (p q : Prop) → Proof (Implies p q) → Proof p → Proof q
end AAACCC

namespace AAADDD
  def Implies (p q : Prop) : Prop := p → q
  structure Proof (p : Prop) : Type where
    proof : p

  axiom implies_intro : (p q : Prop) → (Proof p → Proof q) → Proof (Implies p q)
end AAADDD

namespace AAADDD.mine
  variable (p q : Prop)
  #check p → q

  variable (a b : Type)
  #check a → b

  #check λ x : Prop ↦ x
  #check λ y : Type ↦ y
end AAADDD.mine

namespace AAAEEE
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p := fun hp : p => fun hq : q => hp
end AAAEEE

namespace AAAFFF
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p := fun hp : p => fun hq : q => hp

  #print t1
end AAAFFF

namespace AAAFFF.mine
  theorem t1 : {p : Prop} → {q : Prop} → p → q → p :=
    λ hp _ ↦ hp

  #print t1
end AAAFFF.mine

namespace AAAGGG
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  theorem t1 : p → q → p :=
    fun hp : p =>
    fun hq : q =>
    show p from hp
end AAAGGG

namespace AAAGGG.mine
  theorem t1v1 : {p q : Prop} → p → q → p :=
    λ hp _ ↦ hp

  theorem t1v2 : {p q : Prop} → p → q → p :=
    λ {p _} hp _ ↦ show p from hp
end AAAGGG.mine

namespace AAAHHH
  set_option linter.unusedVariables false

  variable {p : Prop}
  variable {q : Prop}

  theorem t1 (hp : p) (hq : q) : p := hp

  #print t1
end AAAHHH

namespace AAAIII
  set_option linter.unusedVariables false

  variable
    {p : Prop}
    {q : Prop}

  theorem t1 (hp : p) (hq : q) : p := hp

  axiom hp : p

  theorem t2 : q → p := t1 hp
end AAAIII

namespace AAAIII.mine
  def d1 {p q : Prop} (hp : p) (_ : q) :=
    show p from hp

  theorem t1 {p q : Prop} (hp : p) (_ : q) : p :=
    hp
end AAAIII.mine

namespace AAAJJJ
  axiom unsound : False

  theorem ex : 1 = 0 :=
    False.elim unsound
end AAAJJJ

namespace AAAJJJ.mine
  #check False
  #check Sort 0
  #check trivial
  #check True
  #check False.elim
  #check (False.elim)
  #check @False.elim
  #check sorry
  #check (sorry)
  #check @sorry
end AAAJJJ.mine

namespace AAAKKK
  set_option linter.unusedVariables false

  theorem t1 {p q : Prop} (hp : p) (hq : q) : p := hp

  #print t1
end AAAKKK

namespace AAALLL
  set_option linter.unusedVariables false

  theorem t1 : ∀ {p q : Prop}, p → q → p :=
    fun {p q : Prop} (hp : p) (hq : q) => hp
end AAALLL

namespace AAALLL.mine
  theorem t1 : ∀ {p q : Prop}, p → q → p :=
    λ hp _ ↦ hp

  def compose : ∀ {α β γ : Type}, (β → γ) → (α → β) → α → γ :=
    λ g f x ↦ g (f x)

  def double : Nat → Nat :=
    λ x ↦ x + x

  def square : Nat → Nat :=
    λ x ↦ x * x

  #check compose double square 3
  #eval compose double square 3

  #check compose
  #check @compose
  #check (compose)
  #print compose
end AAALLL.mine

namespace AAAMMM
  set_option linter.unusedVariables false

  variable {p q : Prop}

  theorem t1 : p → q → p := fun (hp : p) (hq : q) => hp
end AAAMMM

namespace AAANNN
  variable {p q : Prop}
  variable (hp : p)

  -- theorem t1 : q → p := fun (hq : q) => hp
end AAANNN

namespace AAANNN.mine
  theorem ex {unsound : False} : 1 = 0 :=
    False.elim unsound

  -- variable (absurd : False)
  -- theorem ex2 : 1 = 0 :=
  --   False.elim absurd

  set_option linter.unusedVariables false

  theorem t1 : ∀ {p q : Prop} (hp : p) (hq : q), p :=
    λ hp _ ↦ hp
end AAANNN.mine

namespace AAAOOO
  theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

  variable (p q r s : Prop)

  #check t1 p q
  #check t1 r s
  #check t1 (r → s) (s → r)

  variable (h : r → s)
  #check t1 (r → s) (s → r) h
end AAAOOO

namespace AAAOOO.mine
  axiom unsound1 : False
  theorem ex1 : 1 = 0 := False.elim unsound1
  #check ex1

  theorem ex2 {unsound2 : False} : 1 = 0 := False.elim unsound2
  #check ex2

  variable (unsound3 : False)
  #check @ex2 unsound1
  #check @ex2 unsound3

  -- theorem ex3 : 1 = 0 := False.elim unsound3
  -- theorem ex3 : 1 = 0 := @ex2 unsound3
end AAAOOO.mine

namespace AAAPPP
  variable (p q r s : Prop)

  theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
    fun h₃ : p =>
    show r from h₁ (h₂ h₃)
end AAAPPP

namespace AAAQQQ
  variable (p q : Prop)

  #check p → q → p ∧ q
  #check ¬p → p ↔ False
  #check p ∨ q → q ∨ p
end AAAQQQ

namespace AAARRR
  variable (p q : Prop)

  example (hp : p) (hq : q) : p ∧ q := And.intro hp hq

  #check fun (hp : p) (hq : q) => And.intro hp hq
end AAARRR

namespace AAASSS
  variable (p q : Prop)

  example (h : p ∧ q) : p := And.left h
  example (h : p ∧ q) : q := And.right h
end AAASSS

namespace AAATTT
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    And.intro (And.right h) (And.left h)
end AAATTT

namespace AAATTT.mine
  #check Prod
  #check Nat
  #check Prod Nat Nat
  #check Nat × Nat
  -- #check Prod 1 × 2
  -- #check 1 × 2
  #check (1, 2)

  #check And.intro
  #check True
  #check trivial
  -- #check And.intro True True
  #check And.intro trivial trivial
  -- #check trivial ∧ trivial
  #check True ∧ True
end AAATTT.mine

namespace AAAUUU
  variable (p q : Prop)
  variable (hp : p) (hq : q)

  #check (⟨hp, hq⟩ : p ∧ q)
end AAAUUU

namespace AAAVVV
  variable (xs : List Nat)

  #check List.length xs
  #check xs.length
end AAAVVV

namespace AAAWWW
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    ⟨h.right, h.left⟩
end AAAWWW

namespace AAAWWW.mine
  example : ∀ {p q : Prop}, p ∧ q → q ∧ p :=
    λ h ↦ ⟨h.right, h.left⟩
end AAAWWW.mine

namespace AAAXXX
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, ⟨h.left, h.right⟩⟩

  example (h : p ∧ q) : q ∧ p ∧ q :=
    ⟨h.right, h.left, h.right⟩
end AAAXXX

namespace AAAYYY
  variable (p q : Prop)
  example (hp : p) : p ∨ q := Or.intro_left q hp
  example (hq : q) : p ∨ q := Or.intro_right p hq
end AAAYYY

namespace AAAZZZ
  variable (p q : Prop)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h
      (fun hp : p =>
        show q ∨ p from Or.intro_right q hp)
      (fun hq : q =>
        show q ∨ p from Or.intro_left p hq)
end AAAZZZ

namespace AAAZZZ.mine
  example : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    λ {p q} h ↦ Or.elim h
      (λ hp ↦ Or.intro_right q hp)
      (λ hq ↦ Or.intro_left p hq)
end AAAZZZ.mine

namespace BBBAAA
  variable (p q : Prop)

  example (h : p ∨ q) : q ∨ p :=
    Or.elim h (fun hp => Or.inr hp) (fun hq => Or.inl hq)
end BBBAAA

namespace BBBAAA.mine
  example : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    λ h ↦ Or.elim h (λ hp ↦ Or.inr hp) (λ hq ↦ Or.inl hq)

  example : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    λ h ↦ Or.elim h Or.inr Or.inl
end BBBAAA.mine

namespace BBBBBB
  variable (p q r : Prop)

  example (h : p ∨ q) : q ∨ p :=
    h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq)
end BBBBBB

namespace BBBBBB.mine
  example : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    λ h ↦ h.elim (λ hp ↦ Or.inr hp) (λ hq ↦ Or.inl hq)

  example : ∀ {p q : Prop}, p ∨ q → q ∨ p :=
    λ h ↦ h.elim Or.inr Or.inl
end BBBBBB.mine

namespace BBBCCC
  variable (p q : Prop)

  example (hpq : p → q) (hnq : ¬q) : ¬p :=
    fun hp : p =>
    show False from hnq (hpq hp)
end BBBCCC

namespace BBBCCC.mine
  example : ∀ {p q : Prop}, (p → q) → (¬q → ¬p) :=
    λ hpq hnq hp ↦ show False from hnq (hpq hp)
end BBBCCC.mine

namespace BBBDDD
  variable (p q : Prop)

  example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
end BBBDDD

namespace BBBDDD.mine
  variable (p q : Prop)
  example (hp : p) (hnp : ¬p) : 1 = 0 := False.elim (hnp hp)

  example (hp : p) (hnp : ¬p) : False := hnp hp
end BBBDDD.mine

namespace BBBEEE
  variable (p q : Prop)

  example (hp : p) (hnp : ¬p) : q := absurd hp hnp
end BBBEEE

namespace BBBEEE.mine
  #check absurd

  variable (p : Prop)
  #check ¬p
  -- #print ¬p
end BBBEEE.mine

namespace BBBFFF
  variable (p q r : Prop)

  example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    absurd (hqp hq) hnp
end BBBFFF

namespace BBBFFF.mine
  #check True
  #check True.intro
end BBBFFF.mine

namespace BBBGGG
  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    Iff.intro
      (fun h : p ∧ q =>
        show q ∧ p from And.intro (And.right h) (And.left h))
      (fun h : q ∧ p =>
        show p ∧ q from And.intro (And.right h) (And.left h))

  #check and_swap p q

  variable (h : p ∧ q)
  example : q ∧ p := Iff.mp (and_swap p q) h
end BBBGGG

namespace BBBHHH
  variable (p q : Prop)

  theorem and_swap : p ∧ q ↔ q ∧ p :=
    ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

  example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h
end BBBHHH

namespace BBBHHH.mine
  theorem and_swap : ∀ {p q : Prop}, p ∧ q ↔ q ∧ p :=
    ⟨λ h ↦ ⟨h.right, h.left⟩, λ h ↦ ⟨h.right, h.left⟩⟩

  section variable (p q : Prop)
    #check @and_swap p q
    #check (@and_swap p q).mp
    #check (@and_swap p q).mpr
  end

  example : ∀ {p q : Prop}, p ∧ q → q ∧ p :=
    λ {p q} ↦ (@and_swap p q).mp

  example : ∀ {p q : Prop}, q ∧ p → p ∧ q :=
    λ {p q} ↦ (@and_swap p q).mpr
end BBBHHH.mine

namespace BBBIII
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp
end BBBIII

namespace BBBIII.mine
  example : ∀ {p q : Prop}, p ∧ q → q ∧ p :=
    λ h ↦
      have hp := h.left
      have hq := h.right
    ⟨hq, hp⟩
end BBBIII.mine

namespace BBBJJJ
  variable (p q : Prop)

  example (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    suffices hq : q from And.intro hq hp
    show q from And.right h
end BBBJJJ

namespace BBBJJJ.mine
  example : ∀ {p q : Prop}, p ∧ q → q ∧ p :=
    λ {p q} h ↦
      suffices hp : p from
      suffices hq : q from
    ⟨hq, hp⟩
      show q from h.right
      show p from h.left
end BBBJJJ.mine

namespace BBBKKK
end BBBKKK

namespace BBBLLL
end BBBLLL

namespace BBBMMM
end BBBMMM

namespace BBBNNN
end BBBNNN

namespace BBBOOO
end BBBOOO

namespace BBBPPP
end BBBPPP

namespace BBBQQQ
end BBBQQQ

namespace BBBRRR
end BBBRRR

namespace BBBSSS
end BBBSSS

namespace BBBTTT
end BBBTTT

namespace BBBUUU
end BBBUUU

namespace BBBVVV
end BBBVVV

namespace BBBWWW
end BBBWWW

namespace BBBXXX
end BBBXXX

namespace BBBYYY
end BBBYYY

namespace BBBZZZ
end BBBZZZ

namespace CCCAAA
end CCCAAA

namespace CCCBBB
end CCCBBB

namespace CCCCCC
end CCCCCC

namespace CCCDDD
end CCCDDD

namespace CCCEEE
end CCCEEE

namespace CCCFFF
end CCCFFF

namespace CCCGGG
end CCCGGG

namespace CCCHHH
end CCCHHH

namespace CCCIII
end CCCIII

namespace CCCJJJ
end CCCJJJ

namespace CCCKKK
end CCCKKK

namespace CCCLLL
end CCCLLL

namespace CCCMMM
end CCCMMM

namespace CCCNNN
end CCCNNN

namespace CCCOOO
end CCCOOO

namespace CCCPPP
end CCCPPP

namespace CCCQQQ
end CCCQQQ

namespace CCCRRR
end CCCRRR

namespace CCCSSS
end CCCSSS

namespace CCCTTT
end CCCTTT

namespace CCCUUU
end CCCUUU

namespace CCCVVV
end CCCVVV

namespace CCCWWW
end CCCWWW

namespace CCCXXX
end CCCXXX

namespace CCCYYY
end CCCYYY

namespace CCCZZZ
end CCCZZZ
