include "ct1.mm"
include "t1top.mm"
include "cid.mm"
include "cuni.mm"
include "cin.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "cnt1.mm"
include "resthauslem.mm"

theorem restt1
  let cA: class A
  let cJ: class J
  let cV: class V


  assert |- ( ( J e. Fre /\ A e. V ) -> ( J |`t A ) e. Fre )

  proof
    ct1
    cA
    cJ
    cV
    cJ
    t1top
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
    cnt1
    resthauslem
end
