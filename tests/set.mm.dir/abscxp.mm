include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "clog.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cabs.mm"
include "cre.mm"
include "ccxp.mm"
include "wceq.mm"
include "simpr.mm"
include "relogcl.mm"
include "recnd.mm"
include "adantr.mm"
include "mulcld.mm"
include "absef.mm"
include "syl.mm"
include "cr.mm"
include "remul2.mm"
include "sylan.mm"
include "mulcomd.mm"
include "fveq2d.mm"
include "recl.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "cc0.mm"
include "wne.mm"
include "rpcn.mm"
include "rpne0.mm"
include "cxpef.mm"
include "syl3anc.mm"

theorem abscxp
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. CC ) -> ( abs ` ( A ^c B ) ) = ( A ^c ( Re ` B ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cB
    cA
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cabs
    cfv
    #
    cB
    cre
    cfv
    #
    @3
    cmul
    co
    #
    ce
    cfv
    #
    cA
    cB
    ccxp
    co
    #
    cabs
    cfv
    cA
    @7
    ccxp
    co
    #
    @2
    @6
    @4
    cre
    cfv
    #
    ce
    cfv
    #
    @9
    @2
    @4
    cc
    wcel
    @6
    @13
    wceq
    @2
    cB
    @3
    @0
    @1
    simpr
    #
    @0
    @3
    cc
    wcel
    @1
    @0
    @3
    cA
    relogcl
    #
    recnd
    adantr
    #
    mulcld
    @4
    absef
    syl
    @2
    @12
    @8
    ce
    @2
    @3
    cB
    cmul
    co
    #
    cre
    cfv
    #
    @3
    @7
    cmul
    co
    #
    @12
    @8
    @0
    @3
    cr
    wcel
    @1
    @18
    @19
    wceq
    @15
    @3
    cB
    remul2
    sylan
    @2
    @4
    @17
    cre
    @2
    cB
    @3
    @14
    @16
    mulcomd
    fveq2d
    @2
    @7
    @3
    @2
    @7
    @1
    @7
    cr
    wcel
    @0
    cB
    recl
    adantl
    recnd
    #
    @16
    mulcomd
    3eqtr4d
    fveq2d
    eqtrd
    @2
    @10
    @5
    cabs
    @2
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    @1
    @10
    @5
    wceq
    @0
    @21
    @1
    cA
    rpcn
    adantr
    #
    @0
    @22
    @1
    cA
    rpne0
    adantr
    #
    @14
    cA
    cB
    cxpef
    syl3anc
    fveq2d
    @2
    @21
    @22
    @7
    cc
    wcel
    @11
    @9
    wceq
    @23
    @24
    @20
    cA
    @7
    cxpef
    syl3anc
    3eqtr4d
end
