include "wss.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "xpss1.mm"
include "sslin.mm"
include "syl.mm"
include "df-res.mm"
include "3sstr4g.mm"

theorem ssres2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( C |` A ) C_ ( C |` B ) )

  proof
    cA
    cB
    wss
    #
    cC
    cA
    cvv
    cxp
    #
    cin
    #
    cC
    cB
    cvv
    cxp
    #
    cin
    #
    cC
    cA
    cres
    cC
    cB
    cres
    @0
    @1
    @3
    wss
    @2
    @4
    wss
    cA
    cB
    cvv
    xpss1
    @1
    @3
    cC
    sslin
    syl
    cC
    cA
    df-res
    cC
    cB
    df-res
    3sstr4g
end
