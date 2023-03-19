include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wb.mm"
include "elsn2g.mm"
include "ax-mp.mm"

theorem elsn2
  let cA: class A
  let cB: class B
  assume elsn2.1: |- B e. _V


  assert |- ( A e. { B } <-> A = B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    csn
    wcel
    cA
    cB
    wceq
    wb
    elsn2.1
    cA
    cB
    cvv
    elsn2g
    ax-mp
end
