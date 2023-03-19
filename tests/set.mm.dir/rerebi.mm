include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "rereb.mm"
include "ax-mp.mm"

theorem rerebi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A e. RR <-> ( Re ` A ) = A )

  proof
    cA
    cc
    wcel
    cA
    cr
    wcel
    cA
    cre
    cfv
    cA
    wceq
    wb
    recl.1
    cA
    rereb
    ax-mp
end
