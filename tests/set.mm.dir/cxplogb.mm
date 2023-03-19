include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "clogb.mm"
include "co.mm"
include "ccxp.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cmul.mm"
include "ce.mm"
include "logbval.mm"
include "oveq2d.mm"
include "eldifi.mm"
include "adantr.mm"
include "wne.mm"
include "wn.mm"
include "eldif.mm"
include "wceq.mm"
include "c0ex.mm"
include "prid1.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "necon3bi.mm"
include "adantl.mm"
include "sylbi.mm"
include "snid.mm"
include "anim2i.mm"
include "logcl.mm"
include "syl.mm"
include "w3a.mm"
include "eldifpr.mm"
include "biimpi.mm"
include "logccne0.mm"
include "divcld.mm"
include "cxpefd.mm"
include "eldifsn.mm"
include "divcan1d.mm"
include "fveq2d.mm"
include "eflog.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cxplogb
  let cB: class B
  let cX: class X


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) ) -> ( B ^c ( B logb X ) ) = X )

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
    cX
    cc
    cc0
    csn
    #
    cdif
    wcel
    #
    wa
    #
    cB
    cB
    cX
    clogb
    co
    #
    ccxp
    co
    cB
    cX
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
    ccxp
    co
    @8
    @7
    cmul
    co
    #
    ce
    cfv
    #
    cX
    @4
    @5
    @8
    cB
    ccxp
    cB
    cX
    logbval
    oveq2d
    @4
    cB
    @8
    @1
    cB
    cc
    wcel
    #
    @3
    cB
    cc
    @0
    eldifi
    adantr
    @1
    cB
    cc0
    wne
    #
    @3
    @1
    @11
    cB
    @0
    wcel
    #
    wn
    #
    wa
    #
    @12
    cB
    cc
    @0
    eldif
    #
    @14
    @12
    @11
    @13
    cB
    cc0
    cB
    cc0
    wceq
    @13
    cc0
    @0
    wcel
    cc0
    c1
    c0ex
    prid1
    cB
    cc0
    @0
    eleq1
    mpbiri
    necon3bi
    #
    adantl
    sylbi
    adantr
    @4
    @6
    @7
    @3
    @6
    cc
    wcel
    #
    @1
    @3
    cX
    cc
    wcel
    #
    cX
    cc0
    wne
    #
    wa
    #
    @18
    @3
    @19
    cX
    @2
    wcel
    #
    wn
    #
    wa
    @21
    cX
    cc
    @2
    eldif
    @23
    @20
    @19
    @22
    cX
    cc0
    cX
    cc0
    wceq
    @22
    cc0
    @2
    wcel
    cc0
    c0ex
    snid
    cX
    cc0
    @2
    eleq1
    mpbiri
    necon3bi
    anim2i
    sylbi
    cX
    logcl
    #
    syl
    adantl
    @1
    @7
    cc
    wcel
    #
    @3
    @1
    @11
    @12
    wa
    #
    @25
    @1
    @15
    @26
    @16
    @14
    @12
    @11
    @17
    anim2i
    sylbi
    cB
    logcl
    syl
    adantr
    #
    @4
    @11
    @12
    cB
    c1
    wne
    w3a
    #
    @7
    cc0
    wne
    #
    @1
    @28
    @3
    @1
    @28
    cB
    cc
    cc0
    c1
    eldifpr
    #
    biimpi
    adantr
    cB
    logccne0
    #
    syl
    divcld
    cxpefd
    @4
    @10
    @6
    ce
    cfv
    #
    cX
    @4
    @9
    @6
    ce
    @4
    @6
    @7
    @3
    @18
    @1
    @3
    @21
    @18
    cX
    cc
    cc0
    eldifsn
    #
    @24
    sylbi
    adantl
    @27
    @1
    @29
    @3
    @1
    @28
    @29
    @30
    @31
    sylbi
    adantr
    divcan1d
    fveq2d
    @3
    @32
    cX
    wceq
    #
    @1
    @3
    @21
    @34
    @33
    cX
    eflog
    sylbi
    adantl
    eqtrd
    3eqtrd
end
