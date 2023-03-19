include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "crp.mm"
include "cr.mm"
include "w3a.mm"
include "ccxp.mm"
include "co.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmul.mm"
include "clogb.mm"
include "wceq.mm"
include "logcxp.mm"
include "3adant1.mm"
include "oveq1d.mm"
include "wne.mm"
include "wa.mm"
include "recn.mm"
include "3ad2ant3.mm"
include "rpcn.mm"
include "rpne0.mm"
include "logcld.mm"
include "3ad2ant2.mm"
include "eldifi.mm"
include "eldifpr.mm"
include "simp2bi.mm"
include "logccne0.mm"
include "sylbi.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "divass.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "csn.mm"
include "simp1.mm"
include "adantr.mm"
include "adantl.mm"
include "cxpcld.mm"
include "cxpne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "logbval.mm"
include "syl2anc.mm"
include "rpcndif0.mm"
include "anim2i.mm"
include "3adant3.mm"
include "syl.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem relogbreexp
  let cB: class B
  let cC: class C
  let cE: class E


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ C e. RR+ /\ E e. RR ) -> ( B logb ( C ^c E ) ) = ( E x. ( B logb C ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    #
    cdif
    wcel
    #
    cC
    crp
    wcel
    #
    cE
    cr
    wcel
    #
    w3a
    #
    cC
    cE
    ccxp
    co
    #
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
    cE
    cC
    clog
    cfv
    #
    @7
    cdiv
    co
    #
    cmul
    co
    #
    cB
    @5
    clogb
    co
    #
    cE
    cB
    cC
    clogb
    co
    #
    cmul
    co
    @4
    @8
    cE
    @9
    cmul
    co
    #
    @7
    cdiv
    co
    #
    @11
    @4
    @6
    @14
    @7
    cdiv
    @2
    @3
    @6
    @14
    wceq
    @1
    cC
    cE
    logcxp
    3adant1
    oveq1d
    @4
    cE
    cc
    wcel
    #
    @9
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @7
    cc0
    wne
    #
    wa
    #
    @15
    @11
    wceq
    @3
    @1
    @16
    @2
    cE
    recn
    #
    3ad2ant3
    @2
    @1
    @17
    @3
    @2
    cC
    cC
    rpcn
    #
    cC
    rpne0
    #
    logcld
    3ad2ant2
    @1
    @2
    @20
    @3
    @1
    @18
    @19
    @1
    cB
    cB
    cc
    @0
    eldifi
    @1
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    cB
    cc
    cc0
    c1
    eldifpr
    #
    simp2bi
    logcld
    @1
    @24
    @25
    @26
    w3a
    @19
    @27
    cB
    logccne0
    sylbi
    jca
    3ad2ant1
    cE
    @9
    @7
    divass
    syl3anc
    eqtrd
    @4
    @1
    @5
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @12
    @8
    wceq
    @1
    @2
    @3
    simp1
    @2
    @3
    @29
    @1
    @2
    @3
    wa
    #
    @5
    cc
    wcel
    @5
    cc0
    wne
    @29
    @30
    cC
    cE
    @2
    cC
    cc
    wcel
    @3
    @22
    adantr
    #
    @3
    @16
    @2
    @21
    adantl
    #
    cxpcld
    @30
    cC
    cE
    @31
    @2
    cC
    cc0
    wne
    @3
    @23
    adantr
    @32
    cxpne0d
    @5
    cc
    cc0
    eldifsn
    sylanbrc
    3adant1
    cB
    @5
    logbval
    syl2anc
    @4
    @13
    @10
    cE
    cmul
    @4
    @1
    cC
    @28
    wcel
    #
    wa
    #
    @13
    @10
    wceq
    @1
    @2
    @34
    @3
    @2
    @33
    @1
    cC
    rpcndif0
    anim2i
    3adant3
    cB
    cC
    logbval
    syl
    oveq2d
    3eqtr4d
end
