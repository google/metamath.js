include "cr.mm"
include "wcel.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "wb.mm"
include "lttri2.mm"
include "mp2an.mm"

theorem lttri2i
  let cA: class A
  let cB: class B
  assume lt.1: |- A e. RR
  assume lt.2: |- B e. RR


  assert |- ( A =/= B <-> ( A < B \/ B < A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    wne
    cA
    cB
    clt
    wbr
    cB
    cA
    clt
    wbr
    wo
    wb
    lt.1
    lt.2
    cA
    cB
    lttri2
    mp2an
end
