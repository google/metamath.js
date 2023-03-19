include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "crest.mm"
include "co.mm"
include "cpw.mm"
include "wceq.mm"
include "wss.mm"
include "snssi.mm"
include "resttopon.mm"
include "sylan2.mm"
include "topsn.mm"
include "syl.mm"

theorem restsn2
  let cA: class A
  let cJ: class J
  let cX: class X


  assert |- ( ( J e. ( TopOn ` X ) /\ A e. X ) -> ( J |`t { A } ) = ~P { A } )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    cJ
    cA
    csn
    #
    crest
    co
    #
    @2
    ctopon
    cfv
    wcel
    #
    @3
    @2
    cpw
    wceq
    @1
    @0
    @2
    cX
    wss
    @4
    cA
    cX
    snssi
    @2
    cJ
    cX
    resttopon
    sylan2
    cA
    @3
    topsn
    syl
end
