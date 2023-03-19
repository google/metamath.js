include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cfv.mm"
include "cpw.mm"
include "csuc.mm"
include "wtr.mm"
include "wss.mm"
include "r1tr.mm"
include "dftr4.mm"
include "mpbi.mm"
include "r1suc.mm"
include "syl5sseqr.mm"

theorem r1sssuc
  let cA: class A


  assert |- ( A e. On -> ( R1 ` A ) C_ ( R1 ` suc A ) )

  proof
    cA
    con0
    wcel
    cA
    cr1
    cfv
    #
    cpw
    #
    @0
    cA
    csuc
    cr1
    cfv
    @0
    wtr
    @0
    @1
    wss
    cA
    r1tr
    @0
    dftr4
    mpbi
    cA
    r1suc
    syl5sseqr
end
