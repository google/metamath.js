include "crab.mm"
include "rabex.mm"
include "mptex.mm"

theorem mptrabex
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume mptrabex.1: |- A e. _V

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  assert |- ( x e. { y e. A | ph } |-> B ) e. _V

  proof
    vx
    wph
    vy
    cA
    crab
    cB
    wph
    vy
    cA
    mptrabex.1
    rabex
    mptex
end
