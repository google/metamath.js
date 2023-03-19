include "cha.mm"
include "haustop.mm"
include "cid.mm"
include "cuni.mm"
include "cin.mm"
include "cres.mm"
include "crest.mm"
include "co.mm"
include "cnhaus.mm"
include "resthauslem.mm"

theorem resthaus
  let cA: class A
  let cJ: class J
  let cV: class V


  assert |- ( ( J e. Haus /\ A e. V ) -> ( J |`t A ) e. Haus )

  proof
    cha
    cA
    cJ
    cV
    cJ
    haustop
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
    cnhaus
    resthauslem
end
