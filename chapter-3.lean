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

  theorem t1 : q → p := fun (hq : q) => hp
end AAANNN

namespace AAAOOO
end AAAOOO

namespace AAAPPP
end AAAPPP

namespace AAAQQQ
end AAAQQQ

namespace AAARRR
end AAARRR

namespace AAASSS
end AAASSS

namespace AAATTT
end AAATTT

namespace AAAUUU
end AAAUUU

namespace AAAVVV
end AAAVVV

namespace AAAWWW
end AAAWWW

namespace AAAXXX
end AAAXXX

namespace AAAYYY
end AAAYYY

namespace AAAZZZ
end AAAZZZ

namespace BBBAAA
end BBBAAA

namespace BBBBBB
end BBBBBB

namespace BBBCCC
end BBBCCC

namespace BBBDDD
end BBBDDD

namespace BBBEEE
end BBBEEE

namespace BBBFFF
end BBBFFF

namespace BBBGGG
end BBBGGG

namespace BBBHHH
end BBBHHH

namespace BBBIII
end BBBIII

namespace BBBJJJ
end BBBJJJ

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
