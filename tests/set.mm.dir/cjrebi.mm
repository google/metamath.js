include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "ccj.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "cjreb.mm"
include "ax-mp.mm"

theorem cjrebi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A e. RR <-> ( * ` A ) = A )

  proof
    cA
    cc
    wcel
    cA
    cr
    wcel
    cA
    ccj
    cfv
    cA
    wceq
    wb
    recl.1
    cA
    cjreb
    ax-mp
end
