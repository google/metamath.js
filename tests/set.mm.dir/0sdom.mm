include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "csdm.mm"
include "wbr.mm"
include "wne.mm"
include "wb.mm"
include "0sdomg.mm"
include "ax-mp.mm"

theorem 0sdom
  let cA: class A
  assume 0sdom.1: |- A e. _V


  assert |- ( (/) ~< A <-> A =/= (/) )

  proof
    cA
    cvv
    wcel
    c0
    cA
    csdm
    wbr
    cA
    c0
    wne
    wb
    0sdom.1
    cA
    cvv
    0sdomg
    ax-mp
end
