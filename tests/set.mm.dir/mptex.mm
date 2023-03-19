include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "mptexg.mm"
include "ax-mp.mm"

theorem mptex
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume mptex.1: |- A e. _V

  disjoint A x
  assert |- ( x e. A |-> B ) e. _V

  proof
    cA
    cvv
    wcel
    vx
    cA
    cB
    cmpt
    cvv
    wcel
    mptex.1
    vx
    cA
    cB
    cvv
    mptexg
    ax-mp
end
