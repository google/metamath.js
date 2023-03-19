include "csuc.mm"
include "cale.mm"
include "cfv.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "csdm.mm"
include "wn.mm"
include "alephsucpw2.mm"
include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "fvex.mm"
include "pwex.mm"
include "domtri.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem alephsucpw
  let cA: class A


  assert |- ( aleph ` suc A ) ~<_ ~P ( aleph ` A )

  proof
    cA
    csuc
    #
    cale
    cfv
    #
    cA
    cale
    cfv
    #
    cpw
    #
    cdom
    wbr
    #
    @3
    @1
    csdm
    wbr
    wn
    #
    cA
    alephsucpw2
    @1
    cvv
    wcel
    @3
    cvv
    wcel
    @4
    @5
    wb
    @0
    cale
    fvex
    @2
    cA
    cale
    fvex
    pwex
    @1
    @3
    cvv
    cvv
    domtri
    mp2an
    mpbir
end
