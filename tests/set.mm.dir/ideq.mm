include "cvv.mm"
include "wcel.mm"
include "cid.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "ideqg.mm"
include "ax-mp.mm"

theorem ideq
  let cA: class A
  let cB: class B
  assume ideq.1: |- B e. _V


  assert |- ( A _I B <-> A = B )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cid
    wbr
    cA
    cB
    wceq
    wb
    ideq.1
    cA
    cB
    cvv
    ideqg
    ax-mp
end
