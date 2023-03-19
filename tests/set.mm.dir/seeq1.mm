include "wceq.mm"
include "wse.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "sess1.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem seeq1
  let cA: class A
  let cR: class R
  let cS: class S


  assert |- ( R = S -> ( R Se A <-> S Se A ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cR
    wse
    #
    cA
    cS
    wse
    #
    @0
    cS
    cR
    wss
    @1
    @2
    wi
    cS
    cR
    eqimss2
    cA
    cS
    cR
    sess1
    syl
    @0
    cR
    cS
    wss
    @2
    @1
    wi
    cR
    cS
    eqimss
    cA
    cR
    cS
    sess1
    syl
    impbid
end
