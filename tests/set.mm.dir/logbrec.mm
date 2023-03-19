include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "clogb.mm"
include "clog.mm"
include "cneg.mm"
include "wceq.mm"
include "simpr.mm"
include "rpreccld.mm"
include "relogbval.mm"
include "syldan.mm"
include "negeqd.mm"
include "rpcnd.mm"
include "rpne0d.mm"
include "logcld.mm"
include "cc0.mm"
include "wne.mm"
include "zgt1rpn0n1.mm"
include "simp1d.mm"
include "adantr.mm"
include "relogcld.mm"
include "recnd.mm"
include "simp3d.mm"
include "logne0.mm"
include "syl2anc.mm"
include "divnegd.mm"
include "reccld.mm"
include "recne0d.mm"
include "cc.mm"
include "cim.mm"
include "cpi.mm"
include "reim0d.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "a1i.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "logrec.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "negcon1ad.mm"
include "oveq1d.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"

theorem logbrec
  let cA: class A
  let cB: class B


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ A e. RR+ ) -> ( B logb ( 1 / A ) ) = -u ( B logb A ) )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cA
    crp
    wcel
    #
    wa
    #
    cB
    c1
    cA
    cdiv
    co
    #
    clogb
    co
    #
    @3
    clog
    cfv
    #
    cB
    clog
    cfv
    #
    cdiv
    co
    #
    cB
    cA
    clogb
    co
    #
    cneg
    #
    @0
    @1
    @3
    crp
    wcel
    @4
    @7
    wceq
    @2
    cA
    @0
    @1
    simpr
    #
    rpreccld
    cB
    @3
    relogbval
    syldan
    @2
    @9
    cA
    clog
    cfv
    #
    @6
    cdiv
    co
    #
    cneg
    @11
    cneg
    #
    @6
    cdiv
    co
    @7
    @2
    @8
    @12
    cB
    cA
    relogbval
    negeqd
    @2
    @11
    @6
    @2
    cA
    @2
    cA
    @10
    rpcnd
    #
    @2
    cA
    @10
    rpne0d
    #
    logcld
    @2
    @6
    @2
    cB
    @0
    cB
    crp
    wcel
    #
    @1
    @0
    @16
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    cB
    zgt1rpn0n1
    #
    simp1d
    adantr
    #
    relogcld
    recnd
    @2
    @16
    @18
    @6
    cc0
    wne
    @20
    @0
    @18
    @1
    @0
    @16
    @17
    @18
    @19
    simp3d
    adantr
    cB
    logne0
    syl2anc
    divnegd
    @2
    @13
    @5
    @6
    cdiv
    @2
    @5
    @11
    @2
    @3
    @2
    cA
    @14
    @15
    reccld
    @2
    cA
    @14
    @15
    recne0d
    logcld
    @2
    @11
    @5
    cneg
    #
    @2
    cA
    cc
    wcel
    cA
    cc0
    wne
    @11
    cim
    cfv
    #
    cpi
    wne
    @11
    @21
    wceq
    @14
    @15
    @2
    @22
    cc0
    cpi
    @2
    @11
    @2
    cA
    @10
    relogcld
    reim0d
    @2
    cpi
    cc0
    cpi
    cc0
    wne
    @2
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    necomd
    eqnetrd
    cA
    logrec
    syl3anc
    eqcomd
    negcon1ad
    oveq1d
    3eqtrd
    eqtr4d
end
