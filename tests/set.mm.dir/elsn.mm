include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "wceq.mm"
include "wb.mm"
include "elsng.mm"
include "ax-mp.mm"

theorem elsn
  let cA: class A
  let cB: class B
  assume elsn.1: |- A e. _V


  assert |- ( A e. { B } <-> A = B )

  proof
    cA
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
    elsn.1
    cA
    cB
    cvv
    elsng
    ax-mp
end
