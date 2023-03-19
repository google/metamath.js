include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "reim0b.mm"
include "ax-mp.mm"

theorem reim0bi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A e. RR <-> ( Im ` A ) = 0 )

  proof
    cA
    cc
    wcel
    cA
    cr
    wcel
    cA
    cim
    cfv
    cc0
    wceq
    wb
    recl.1
    cA
    reim0b
    ax-mp
end
