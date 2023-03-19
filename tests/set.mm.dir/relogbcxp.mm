include "crp.mm"
include "c1.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "ccxp.mm"
include "co.mm"
include "clogb.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmul.mm"
include "cc.mm"
include "cc0.mm"
include "cpr.mm"
include "wceq.mm"
include "wne.mm"
include "eldifsn.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "simpr.mm"
include "eldifpr.mm"
include "syl3anbrc.mm"
include "sylbi.mm"
include "eldifi.mm"
include "syl.mm"
include "recn.mm"
include "cxpcl.mm"
include "syl2an.mm"
include "adantl.mm"
include "cxpne0d.mm"
include "sylanbrc.mm"
include "logbval.mm"
include "syl2anc.mm"
include "logcxp.mm"
include "sylan.mm"
include "oveq1d.mm"
include "wn.mm"
include "eldif.mm"
include "rpcnne0.mm"
include "logcl.mm"
include "logne0.mm"
include "divcan4d.mm"
include "3eqtrd.mm"

theorem relogbcxp
  let cB: class B
  let cX: class X


  assert |- ( ( B e. ( RR+ \ { 1 } ) /\ X e. RR ) -> ( B logb ( B ^c X ) ) = X )

  proof
    cB
    crp
    c1
    csn
    #
    cdif
    wcel
    #
    cX
    cr
    wcel
    #
    wa
    #
    cB
    cB
    cX
    ccxp
    co
    #
    clogb
    co
    #
    @4
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
    cX
    @7
    cmul
    co
    #
    @7
    cdiv
    co
    cX
    @3
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    #
    @4
    cc
    cc0
    csn
    cdif
    wcel
    #
    @5
    @8
    wceq
    @1
    @10
    @2
    @1
    cB
    crp
    wcel
    #
    cB
    c1
    wne
    #
    wa
    #
    @10
    cB
    crp
    c1
    eldifsn
    #
    @14
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    @13
    @10
    @12
    @16
    @13
    cB
    rpcn
    #
    adantr
    @12
    @17
    @13
    cB
    rpne0
    adantr
    #
    @12
    @13
    simpr
    cB
    cc
    cc0
    c1
    eldifpr
    syl3anbrc
    sylbi
    adantr
    @3
    @4
    cc
    wcel
    #
    @4
    cc0
    wne
    @11
    @1
    @16
    cX
    cc
    wcel
    #
    @20
    @2
    @1
    @12
    @16
    cB
    crp
    @0
    eldifi
    #
    @18
    syl
    #
    cX
    recn
    #
    cB
    cX
    cxpcl
    syl2an
    @3
    cB
    cX
    @1
    @16
    @2
    @23
    adantr
    @1
    @17
    @2
    @1
    @14
    @17
    @15
    @19
    sylbi
    adantr
    @2
    @21
    @1
    @24
    adantl
    #
    cxpne0d
    @4
    cc
    cc0
    eldifsn
    sylanbrc
    cB
    @4
    logbval
    syl2anc
    @3
    @6
    @9
    @7
    cdiv
    @1
    @12
    @2
    @6
    @9
    wceq
    @22
    cB
    cX
    logcxp
    sylan
    oveq1d
    @3
    cX
    @7
    @25
    @1
    @7
    cc
    wcel
    #
    @2
    @1
    @16
    @17
    wa
    #
    @26
    @1
    @12
    cB
    @0
    wcel
    wn
    #
    wa
    @27
    cB
    crp
    @0
    eldif
    @12
    @27
    @28
    cB
    rpcnne0
    adantr
    sylbi
    cB
    logcl
    syl
    adantr
    @1
    @7
    cc0
    wne
    #
    @2
    @1
    @14
    @29
    @15
    cB
    logne0
    sylbi
    adantr
    divcan4d
    3eqtrd
end
