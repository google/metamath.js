include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "n0i.mm"
include "ax-mp.mm"

theorem n0ii
  let cA: class A
  let cB: class B
  assume n0ii.1: |- A e. B


  assert |- -. B = (/)

  proof
    cA
    cB
    wcel
    cB
    c0
    wceq
    wn
    n0ii.1
    cB
    cA
    n0i
    ax-mp
end
