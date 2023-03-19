include "csn.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "c0.mm"
include "cpr.mm"
include "wss.mm"
include "topgele.mm"
include "simprd.mm"
include "pwsn.mm"
include "simpld.mm"
include "syl5eqss.mm"
include "eqssd.mm"

theorem topsn
  let cA: class A
  let cJ: class J


  assert |- ( J e. ( TopOn ` { A } ) -> J = ~P { A } )

  proof
    cJ
    cA
    csn
    #
    ctopon
    cfv
    wcel
    #
    cJ
    @0
    cpw
    #
    @1
    c0
    @0
    cpr
    #
    cJ
    wss
    #
    cJ
    @2
    wss
    #
    cJ
    @0
    topgele
    #
    simprd
    @1
    @2
    @3
    cJ
    cA
    pwsn
    @1
    @4
    @5
    @6
    simpld
    syl5eqss
    eqssd
end
