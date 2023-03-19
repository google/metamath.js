include "wceq.mm"
include "wpo.mm"
include "wss.mm"
include "wi.mm"
include "eqimss2.mm"
include "poss.mm"
include "syl.mm"
include "eqimss.mm"
include "impbid.mm"

theorem poeq2
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( A = B -> ( R Po A <-> R Po B ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cR
    wpo
    #
    cB
    cR
    wpo
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
    poss
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
    poss
    syl
    impbid
end
