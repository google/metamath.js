include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "clogb.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cc.mm"
include "wne.mm"
include "crp.mm"
include "w3a.mm"
include "zgt1rpn0n1.mm"
include "adantr.mm"
include "simp1d.mm"
include "rpcnd.mm"
include "simp2d.mm"
include "simp3d.mm"
include "logb1.mm"
include "syl3anc.mm"
include "simpr.mm"
include "oveq2d.mm"
include "exp0d.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"
include "clog.mm"
include "cdiv.mm"
include "cmul.mm"
include "cpr.mm"
include "cdif.mm"
include "csn.mm"
include "eldifpr.mm"
include "syl3anbrc.mm"
include "rpexpcld.mm"
include "rpcnne0d.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "logbval.mm"
include "syl2anc.mm"
include "ccxp.mm"
include "cr.mm"
include "zred.mm"
include "logcxpd.mm"
include "cxpexpzd.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "oveq1d.mm"
include "recnd.mm"
include "logcld.mm"
include "logne0.mm"
include "divcan4d.mm"
include "3eqtr2d.mm"
include "pm2.61dane.mm"

theorem nnlogbexp
  let cB: class B
  let cM: class M


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ M e. ZZ ) -> ( B logb ( B ^ M ) ) = M )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    #
    cB
    cB
    cM
    cexp
    co
    #
    clogb
    co
    #
    cM
    wceq
    cM
    cc0
    @2
    cM
    cc0
    wceq
    #
    wa
    #
    cB
    c1
    clogb
    co
    #
    cc0
    @4
    cM
    @6
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
    @7
    cc0
    wceq
    @2
    @8
    @5
    @2
    cB
    @2
    cB
    crp
    wcel
    #
    @9
    @10
    @0
    @11
    @9
    @10
    w3a
    @1
    cB
    zgt1rpn0n1
    adantr
    #
    simp1d
    #
    rpcnd
    #
    adantr
    #
    @2
    @9
    @5
    @2
    @11
    @9
    @10
    @12
    simp2d
    #
    adantr
    @2
    @10
    @5
    @2
    @11
    @9
    @10
    @12
    simp3d
    #
    adantr
    cB
    logb1
    syl3anc
    @6
    @3
    c1
    cB
    clogb
    @6
    @3
    cB
    cc0
    cexp
    co
    c1
    @6
    cM
    cc0
    cB
    cexp
    @2
    @5
    simpr
    #
    oveq2d
    @6
    cB
    @15
    exp0d
    eqtrd
    oveq2d
    @18
    3eqtr4d
    @2
    cM
    cc0
    wne
    #
    wa
    #
    @4
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
    cM
    @22
    cmul
    co
    #
    @22
    cdiv
    co
    cM
    @20
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @3
    cc
    cc0
    csn
    cdif
    wcel
    #
    @4
    @23
    wceq
    @20
    @8
    @9
    @10
    @25
    @2
    @8
    @19
    @14
    adantr
    #
    @2
    @9
    @19
    @16
    adantr
    #
    @2
    @10
    @19
    @17
    adantr
    #
    cB
    cc
    cc0
    c1
    eldifpr
    syl3anbrc
    @20
    @3
    cc
    wcel
    @3
    cc0
    wne
    wa
    @26
    @20
    @3
    @20
    cB
    cM
    @2
    @11
    @19
    @13
    adantr
    #
    @2
    @1
    @19
    @0
    @1
    simpr
    #
    adantr
    #
    rpexpcld
    rpcnne0d
    @3
    cc
    cc0
    eldifsn
    sylibr
    cB
    @3
    logbval
    syl2anc
    @20
    @24
    @21
    @22
    cdiv
    @20
    cB
    cM
    ccxp
    co
    #
    clog
    cfv
    @24
    @21
    @20
    cB
    cM
    @30
    @2
    cM
    cr
    wcel
    @19
    @2
    cM
    @31
    zred
    adantr
    #
    logcxpd
    @20
    @33
    @3
    clog
    @20
    cB
    cM
    @27
    @28
    @32
    cxpexpzd
    fveq2d
    eqtr3d
    oveq1d
    @20
    cM
    @22
    @20
    cM
    @34
    recnd
    @20
    cB
    @27
    @28
    logcld
    @20
    @11
    @10
    @22
    cc0
    wne
    @30
    @29
    cB
    logne0
    syl2anc
    divcan4d
    3eqtr2d
    pm2.61dane
end
