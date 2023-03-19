include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "ax-mp.mm"

theorem ne0ii
  let cA: class A
  let cB: class B
  assume n0ii.1: |- A e. B


  assert |- B =/= (/)

  proof
    cA
    cB
    wcel
    cB
    c0
    wne
    n0ii.1
    cB
    cA
    ne0i
    ax-mp
end
