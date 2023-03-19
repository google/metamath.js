include "ct0.mm"
include "t0top.mm"
include "cid.mm"
include "cuni.mm"
include "cin.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "cnt0.mm"
include "resthauslem.mm"

theorem restt0
  let cA: class A
  let cJ: class J
  let cV: class V


  assert |- ( ( J e. Kol2 /\ A e. V ) -> ( J |`t A ) e. Kol2 )

  proof
    ct0
    cA
    cJ
    cV
    cJ
    t0top
    cid
    cA
    cJ
    cuni
    cin
    #
    cres
    cJ
    cA
    crest
    co
    cJ
    @0
    @0
    cnt0
    resthauslem
end
