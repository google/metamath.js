include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "clog.mm"
include "cfv.mm"
include "cim.mm"
include "cpi.mm"
include "w3a.mm"
include "ce.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "wceq.mm"
include "wa.mm"
include "reccl.mm"
include "recne0.mm"
include "eflog.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "recrec.mm"
include "eqtr4d.mm"
include "logcld.mm"
include "efneg.mm"
include "syl.mm"
include "3eqtr4d.mm"
include "3adant3.mm"
include "fveq2d.mm"
include "crn.mm"
include "logrncl.mm"
include "logef.mm"
include "wn.mm"
include "df-ne.mm"
include "crp.mm"
include "wb.mm"
include "lognegb.mm"
include "biimprd.mm"
include "ax-1cn.mm"
include "divneg2.mm"
include "mp3an1.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "wi.mm"
include "negcl.mm"
include "adantr.mm"
include "negeq0.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "rpreccl.mm"
include "syl5ib.mm"
include "syld.mm"
include "con3d.mm"
include "3impia.mm"
include "syl3an3b.mm"
include "logreclem.mm"
include "stoic3.mm"
include "syld3an3.mm"
include "3eqtr3d.mm"

theorem logrec
  let cA: class A


  assert |- ( ( A e. CC /\ A =/= 0 /\ ( Im ` ( log ` A ) ) =/= _pi ) -> ( log ` A ) = -u ( log ` ( 1 / A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    clog
    cfv
    #
    cim
    cfv
    #
    cpi
    wne
    #
    w3a
    #
    @2
    ce
    cfv
    #
    clog
    cfv
    #
    c1
    cA
    cdiv
    co
    #
    clog
    cfv
    #
    cneg
    #
    ce
    cfv
    #
    clog
    cfv
    #
    @2
    @10
    @5
    @6
    @11
    clog
    @0
    @1
    @6
    @11
    wceq
    @4
    @0
    @1
    wa
    #
    c1
    @8
    cdiv
    co
    #
    c1
    @9
    ce
    cfv
    #
    cdiv
    co
    #
    @6
    @11
    @13
    @8
    @15
    c1
    cdiv
    @13
    @15
    @8
    @13
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    @15
    @8
    wceq
    cA
    reccl
    #
    cA
    recne0
    #
    @8
    eflog
    syl2anc
    eqcomd
    oveq2d
    @13
    @6
    cA
    @14
    cA
    eflog
    cA
    recrec
    eqtr4d
    @13
    @9
    cc
    wcel
    @11
    @16
    wceq
    @13
    @8
    @19
    @20
    logcld
    @9
    efneg
    syl
    3eqtr4d
    3adant3
    fveq2d
    @5
    @2
    clog
    crn
    #
    wcel
    #
    @7
    @2
    wceq
    @0
    @1
    @22
    @4
    cA
    logrncl
    3adant3
    @2
    logef
    syl
    @5
    @10
    @21
    wcel
    #
    @12
    @10
    wceq
    @0
    @1
    @4
    @9
    cim
    cfv
    cpi
    wceq
    #
    wn
    #
    @23
    @4
    @0
    @1
    @3
    cpi
    wceq
    #
    wn
    #
    @25
    @3
    cpi
    df-ne
    @0
    @1
    @27
    @25
    @13
    @24
    @26
    @13
    @24
    cA
    cneg
    #
    crp
    wcel
    #
    @26
    @13
    @24
    c1
    @28
    cdiv
    co
    #
    crp
    wcel
    #
    @29
    @13
    @24
    @8
    cneg
    #
    crp
    wcel
    #
    @31
    @13
    @33
    @24
    @13
    @17
    @18
    @33
    @24
    wb
    @19
    @20
    @8
    lognegb
    syl2anc
    biimprd
    @13
    @32
    @30
    crp
    c1
    cc
    wcel
    @0
    @1
    @32
    @30
    wceq
    ax-1cn
    c1
    cA
    divneg2
    mp3an1
    eleq1d
    sylibd
    @13
    @28
    cc
    wcel
    #
    @28
    cc0
    wne
    #
    @31
    @29
    wi
    @0
    @34
    @1
    cA
    negcl
    adantr
    @0
    @1
    @35
    @0
    cA
    cc0
    @28
    cc0
    cA
    negeq0
    necon3bid
    biimpa
    @31
    c1
    @30
    cdiv
    co
    #
    crp
    wcel
    @34
    @35
    wa
    #
    @29
    @30
    rpreccl
    @37
    @36
    @28
    crp
    @28
    recrec
    eleq1d
    syl5ib
    syl2anc
    syld
    cA
    lognegb
    sylibd
    con3d
    3impia
    syl3an3b
    @0
    @1
    @9
    @21
    wcel
    #
    @25
    @23
    @13
    @17
    @18
    @38
    @19
    @20
    @8
    logrncl
    syl2anc
    @9
    logreclem
    stoic3
    syld3an3
    @10
    logef
    syl
    3eqtr3d
end
