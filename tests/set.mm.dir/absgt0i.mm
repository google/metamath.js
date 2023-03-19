include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "absgt0.mm"
include "ax-mp.mm"

theorem absgt0i
  let cA: class A
  assume absvalsqi.1: |- A e. CC


  assert |- ( A =/= 0 <-> 0 < ( abs ` A ) )

  proof
    cA
    cc
    wcel
    cA
    cc0
    wne
    cc0
    cA
    cabs
    cfv
    clt
    wbr
    wb
    absvalsqi.1
    cA
    absgt0
    ax-mp
end
