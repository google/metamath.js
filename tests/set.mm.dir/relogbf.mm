include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "clogb.mm"
include "ccur.mm"
include "cfv.mm"
include "cres.mm"
include "wf.mm"
include "cv.mm"
include "cdm.mm"
include "wral.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "rpcndif0.mm"
include "adantl.mm"
include "wceq.mm"
include "clog.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "wne.mm"
include "w3a.mm"
include "rpcn.mm"
include "adantr.mm"
include "rpne0.mm"
include "wo.mm"
include "simpr.mm"
include "olcd.mm"
include "wb.mm"
include "rpre.mm"
include "1red.mm"
include "lttri2.mm"
include "syl2an.mm"
include "mpbird.mm"
include "3jca.mm"
include "logbmpt.mm"
include "syl.mm"
include "dmeqd.mm"
include "cvv.mm"
include "ovexd.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "logbfval.mm"
include "simpll.mm"
include "relogbcl.mm"
include "eqeltrd.mm"
include "jca.mm"
include "wfun.mm"
include "logbf.mm"
include "ffun.mm"
include "ffvresb.mm"
include "3syl.mm"

theorem relogbf
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cX: class X


  assert |- ( ( B e. RR+ /\ 1 < B ) -> ( ( curry logb ` B ) |` RR+ ) : RR+ --> RR )

  proof
    cB
    crp
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    wa
    #
    crp
    cr
    cB
    clogb
    ccur
    cfv
    #
    crp
    cres
    wf
    #
    vx
    cv
    #
    @3
    cdm
    #
    wcel
    #
    @5
    @3
    cfv
    #
    cr
    wcel
    #
    wa
    #
    vx
    crp
    wral
    #
    @2
    @10
    vx
    crp
    @2
    @5
    crp
    wcel
    #
    wa
    #
    @7
    @9
    @13
    @5
    cc
    cc0
    csn
    cdif
    #
    @6
    @12
    @5
    @14
    wcel
    #
    @2
    @5
    rpcndif0
    #
    adantl
    @2
    @6
    @14
    wceq
    @12
    @2
    @6
    vx
    @14
    @5
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
    cmpt
    #
    cdm
    #
    @14
    @2
    @3
    @20
    @2
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
    w3a
    #
    @3
    @20
    wceq
    @2
    @22
    @23
    @24
    @0
    @22
    @1
    cB
    rpcn
    adantr
    @0
    @23
    @1
    cB
    rpne0
    adantr
    @2
    @24
    cB
    c1
    clt
    wbr
    #
    @1
    wo
    #
    @2
    @1
    @26
    @0
    @1
    simpr
    olcd
    @0
    cB
    cr
    wcel
    c1
    cr
    wcel
    @24
    @27
    wb
    @1
    cB
    rpre
    @1
    1red
    cB
    c1
    lttri2
    syl2an
    mpbird
    #
    3jca
    #
    vx
    cB
    logbmpt
    syl
    dmeqd
    @2
    @19
    cvv
    wcel
    #
    vx
    @14
    wral
    @21
    @14
    wceq
    @2
    @30
    vx
    @14
    @2
    @15
    wa
    @17
    @18
    cdiv
    ovexd
    ralrimiva
    vx
    @14
    @19
    cvv
    dmmptg
    syl
    eqtrd
    adantr
    eleqtrrd
    @13
    @8
    cB
    @5
    clogb
    co
    #
    cr
    @2
    @25
    @15
    @8
    @31
    wceq
    @12
    @29
    @16
    cB
    @5
    logbfval
    syl2an
    @13
    @0
    @12
    @24
    w3a
    @31
    cr
    wcel
    @13
    @0
    @12
    @24
    @0
    @1
    @12
    simpll
    @2
    @12
    simpr
    @2
    @24
    @12
    @28
    adantr
    3jca
    cB
    @5
    relogbcl
    syl
    eqeltrd
    jca
    ralrimiva
    @2
    @14
    cc
    @3
    wf
    #
    @3
    wfun
    @4
    @11
    wb
    @2
    @25
    @32
    @29
    cB
    logbf
    syl
    @14
    cc
    @3
    ffun
    vx
    crp
    cr
    @3
    ffvresb
    3syl
    mpbird
end
