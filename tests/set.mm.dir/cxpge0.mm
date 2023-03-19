include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "ccxp.mm"
include "co.mm"
include "wa.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "0re.mm"
include "leloe.mm"
include "mpan.mm"
include "adantr.mm"
include "crp.mm"
include "wi.mm"
include "elrp.mm"
include "rpcxpcl.mm"
include "rpge0d.mm"
include "ex.mm"
include "sylbir.mm"
include "impancom.mm"
include "c1.mm"
include "0le1.mm"
include "cc.mm"
include "0cn.mm"
include "cxp0.mm"
include "ax-mp.mm"
include "breqtrri.mm"
include "simpr.mm"
include "oveq2d.mm"
include "syl5breqr.mm"
include "wne.mm"
include "0le0.mm"
include "recn.mm"
include "0cxp.mm"
include "sylan.mm"
include "pm2.61dane.mm"
include "adantl.mm"
include "oveq1.mm"
include "breq2d.mm"
include "syl5ibcom.mm"
include "jaod.mm"
include "sylbid.mm"
include "3impia.mm"
include "3com23.mm"

theorem cxpge0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ 0 <_ A /\ B e. RR ) -> 0 <_ ( A ^c B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cA
    cB
    ccxp
    co
    #
    cle
    wbr
    #
    @0
    @1
    @2
    @4
    @0
    @1
    wa
    #
    @2
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    #
    @4
    @0
    @2
    @8
    wb
    #
    @1
    cc0
    cr
    wcel
    @0
    @9
    0re
    cc0
    cA
    leloe
    mpan
    adantr
    @5
    @6
    @4
    @7
    @0
    @6
    @1
    @4
    @0
    @6
    wa
    cA
    crp
    wcel
    #
    @1
    @4
    wi
    cA
    elrp
    @10
    @1
    @4
    @10
    @1
    wa
    @3
    cA
    cB
    rpcxpcl
    rpge0d
    ex
    sylbir
    impancom
    @5
    cc0
    cc0
    cB
    ccxp
    co
    #
    cle
    wbr
    #
    @7
    @4
    @1
    @12
    @0
    @1
    @12
    cB
    cc0
    @1
    cB
    cc0
    wceq
    #
    wa
    #
    cc0
    cc0
    cc0
    ccxp
    co
    #
    @11
    cle
    cc0
    c1
    @15
    cle
    0le1
    cc0
    cc
    wcel
    @15
    c1
    wceq
    0cn
    cc0
    cxp0
    ax-mp
    breqtrri
    @14
    cB
    cc0
    cc0
    ccxp
    @1
    @13
    simpr
    oveq2d
    syl5breqr
    @1
    cB
    cc0
    wne
    #
    wa
    cc0
    cc0
    @11
    cle
    0le0
    @1
    cB
    cc
    wcel
    @16
    @11
    cc0
    wceq
    cB
    recn
    cB
    0cxp
    sylan
    syl5breqr
    pm2.61dane
    adantl
    @7
    @11
    @3
    cc0
    cle
    cc0
    cA
    cB
    ccxp
    oveq1
    breq2d
    syl5ibcom
    jaod
    sylbid
    3impia
    3com23
end
