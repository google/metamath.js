include "wss.mm"
include "cid.mm"
include "cres.mm"
include "cxp.mm"
include "resss.mm"
include "a1i.mm"
include "idssxp.mm"
include "xpss2.mm"
include "syl5ss.mm"
include "ssind.mm"

theorem idresssidinxp
  let cA: class A
  let cB: class B


  assert |- ( A C_ B -> ( _I |` A ) C_ ( _I i^i ( A X. B ) ) )

  proof
    cA
    cB
    wss
    #
    cid
    cA
    cres
    #
    cid
    cA
    cB
    cxp
    #
    @1
    cid
    wss
    @0
    cid
    cA
    resss
    a1i
    @0
    @1
    cA
    cA
    cxp
    @2
    cA
    idssxp
    cA
    cB
    cA
    xpss2
    syl5ss
    ssind
end
