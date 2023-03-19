include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "rpcn.mm"
include "cxpcl.mm"
include "sylan.mm"
include "rpreccl.mm"
include "rpcnd.mm"
include "cc0.mm"
include "wne.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "cxpne0.mm"
include "syl3anc.mm"
include "cmul.mm"
include "recidd.mm"
include "oveq1d.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "rprege0.mm"
include "rprege0d.mm"
include "mulcxp.mm"
include "1cxp.mm"
include "syl.mm"
include "3eqtr3d.mm"
include "mvllmuld.mm"

theorem cxprec
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR+ /\ B e. CC ) -> ( ( 1 / A ) ^c B ) = ( 1 / ( A ^c B ) ) )

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
    cA
    cB
    ccxp
    co
    #
    c1
    cA
    cdiv
    co
    #
    cB
    ccxp
    co
    #
    c1
    @0
    cA
    cc
    wcel
    #
    @1
    @3
    cc
    wcel
    cA
    rpcn
    #
    cA
    cB
    cxpcl
    sylan
    @0
    @4
    cc
    wcel
    @1
    @5
    cc
    wcel
    @0
    @4
    cA
    rpreccl
    #
    rpcnd
    @4
    cB
    cxpcl
    sylan
    @2
    @6
    cA
    cc0
    wne
    #
    @1
    @3
    cc0
    wne
    @0
    @6
    @1
    @7
    adantr
    #
    @0
    @9
    @1
    cA
    rpne0
    adantr
    #
    @0
    @1
    simpr
    #
    cA
    cB
    cxpne0
    syl3anc
    @2
    cA
    @4
    cmul
    co
    #
    cB
    ccxp
    co
    #
    c1
    cB
    ccxp
    co
    #
    @3
    @5
    cmul
    co
    #
    c1
    @2
    @13
    c1
    cB
    ccxp
    @2
    cA
    @10
    @11
    recidd
    oveq1d
    @2
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    wa
    #
    @4
    cr
    wcel
    cc0
    @4
    cle
    wbr
    wa
    #
    @1
    @14
    @16
    wceq
    @0
    @17
    @1
    cA
    rprege0
    adantr
    @0
    @18
    @1
    @0
    @4
    @8
    rprege0d
    adantr
    @12
    cA
    @4
    cB
    mulcxp
    syl3anc
    @2
    @1
    @15
    c1
    wceq
    @12
    cB
    1cxp
    syl
    3eqtr3d
    mvllmuld
end
