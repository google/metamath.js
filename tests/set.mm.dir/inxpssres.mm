include "cxp.mm"
include "cin.mm"
include "cvv.mm"
include "cres.mm"
include "wss.mm"
include "ssid.mm"
include "ssv.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sslin.mm"
include "ax-mp.mm"
include "df-res.mm"
include "sseqtr4i.mm"

theorem inxpssres
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( R i^i ( A X. B ) ) C_ ( R |` A )

  proof
    cR
    cA
    cB
    cxp
    #
    cin
    #
    cR
    cA
    cvv
    cxp
    #
    cin
    #
    cR
    cA
    cres
    @0
    @2
    wss
    #
    @1
    @3
    wss
    cA
    cA
    wss
    cB
    cvv
    wss
    @4
    cA
    ssid
    cB
    ssv
    cA
    cA
    cB
    cvv
    xpss12
    mp2an
    @0
    @2
    cR
    sslin
    ax-mp
    cR
    cA
    df-res
    sseqtr4i
end
