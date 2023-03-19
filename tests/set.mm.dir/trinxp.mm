include "ccom.mm"
include "wss.mm"
include "cxp.mm"
include "cin.mm"
include "xpidtr.mm"
include "trin2.mm"
include "mpan2.mm"

theorem trinxp
  let cA: class A
  let cR: class R


  assert |- ( ( R o. R ) C_ R -> ( ( R i^i ( A X. A ) ) o. ( R i^i ( A X. A ) ) ) C_ ( R i^i ( A X. A ) ) )

  proof
    cR
    cR
    ccom
    cR
    wss
    cA
    cA
    cxp
    #
    @0
    ccom
    @0
    wss
    cR
    @0
    cin
    #
    @1
    ccom
    @1
    wss
    cA
    xpidtr
    cR
    @0
    trin2
    mpan2
end
