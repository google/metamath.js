include "wceq.mm"
include "wfr.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "frss.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem freq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R Fr A <-> R Fr B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cR
    wfr
    #
    cB
    cR
    wfr
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
    frss
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
    frss
    syl
    impbid
end
