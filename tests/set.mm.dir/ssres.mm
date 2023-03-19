include "wss.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "ssrin.mm"
include "df-res.mm"
include "3sstr4g.mm"

theorem ssres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( A |` C ) C_ ( B |` C ) )

  proof
    cA
    cB
    wss
    cA
    cC
    cvv
    cxp
    #
    cin
    cB
    @0
    cin
    cA
    cC
    cres
    cB
    cC
    cres
    cA
    cB
    @0
    ssrin
    cA
    cC
    df-res
    cB
    cC
    df-res
    3sstr4g
end
