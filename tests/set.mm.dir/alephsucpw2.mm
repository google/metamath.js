include "cale.mm"
include "cfv.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "csuc.mm"
include "fvex.mm"
include "canth2.mm"
include "alephnbtwn2.mm"
include "mptnan.mm"

theorem alephsucpw2
  let cA: class A


  assert |- -. ~P ( aleph ` A ) ~< ( aleph ` suc A )

  proof
    cA
    cale
    cfv
    #
    @0
    cpw
    #
    csdm
    wbr
    @1
    cA
    csuc
    cale
    cfv
    csdm
    wbr
    @0
    cA
    cale
    fvex
    canth2
    cA
    @1
    alephnbtwn2
    mptnan
end
