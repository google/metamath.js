include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "wb.mm"
include "posdif.mm"
include "mp2an.mm"

theorem posdifi
  let cA: class A
  let cB: class B
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR


  assert |- ( A < B <-> 0 < ( B - A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    clt
    wbr
    cc0
    cB
    cA
    cmin
    co
    clt
    wbr
    wb
    lt2.1
    lt2.2
    cA
    cB
    posdif
    mp2an
end
