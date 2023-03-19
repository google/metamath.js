include "wceq.mm"
include "wse.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "sess2.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem seeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R Se A <-> R Se B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cR
    wse
    #
    cB
    cR
    wse
    #
    @0
    cB
    cA
    wss
    @1
    @2
    wi
    cB
    cA
    eqimss2
    cB
    cA
    cR
    sess2
    syl
    @0
    cA
    cB
    wss
    @2
    @1
    wi
    cA
    cB
    eqimss
    cA
    cB
    cR
    sess2
    syl
    impbid
end
