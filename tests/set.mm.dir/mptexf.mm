include "cvv.mm"
include "wcel.mm"
include "cmpt.mm"
include "mptexgf.mm"
include "ax-mp.mm"

theorem mptexf
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume mptexf.1: |- F/_ x A
  assume mptexf.2: |- A e. _V


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
    mptexf.2
    vx
    cA
    cB
    cvv
    mptexf.1
    mptexgf
    ax-mp
end
