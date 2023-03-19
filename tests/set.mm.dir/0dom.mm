include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cdom.mm"
include "wbr.mm"
include "0domg.mm"
include "ax-mp.mm"

theorem 0dom
  let cA: class A
  assume 0sdom.1: |- A e. _V


  assert |- (/) ~<_ A

  proof
    cA
    cvv
    wcel
    c0
    cA
    cdom
    wbr
    0sdom.1
    cA
    cvv
    0domg
    ax-mp
end
