include "cz.mm"
include "crest.mm"
include "co.mm"
include "cpw.mm"
include "restsspw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "c1.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "cin.mm"
include "cc.mm"
include "elpwi.mm"
include "sselda.mm"
include "zcnd.mm"
include "cxmt.mm"
include "cxr.mm"
include "cnxmet.mm"
include "crp.mm"
include "1rp.mm"
include "rpxr.mm"
include "ax-mp.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "mp3an13.mm"
include "ctop.mm"
include "cvv.mm"
include "cnfldtop.mm"
include "zex.mm"
include "elrestr.mm"
include "mp3an12.mm"
include "3syl.mm"
include "blcntr.mm"
include "syl.mm"
include "elind.mm"
include "adantr.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "zsubcld.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "syl2anc.mm"
include "inss1.mm"
include "wb.mm"
include "elbl2.mm"
include "mpanl12.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "cn0.mm"
include "nn0abscl.mm"
include "nn0lt10b.mm"
include "abs00d.mm"
include "subeq0d.mm"
include "simplr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ralrimiva.mm"
include "resttop.mm"
include "mp2an.mm"
include "eltop2.mm"
include "sylibr.mm"
include "ssriv.mm"
include "eqssi.mm"

theorem zdis
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- ( J |`t ZZ ) = ~P ZZ

  proof
    cJ
    cz
    crest
    co
    #
    cz
    cpw
    #
    cz
    cJ
    restsspw
    vx
    @1
    @0
    vx
    cv
    #
    @1
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wcel
    #
    @5
    @2
    wss
    #
    wa
    #
    vz
    @0
    wrex
    #
    vy
    @2
    wral
    #
    @2
    @0
    wcel
    #
    @3
    @9
    vy
    @2
    @3
    @4
    @2
    wcel
    #
    wa
    #
    @4
    c1
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    cz
    cin
    #
    @0
    wcel
    #
    @4
    @16
    wcel
    #
    @16
    @2
    wss
    #
    @9
    @13
    @4
    cc
    wcel
    #
    @15
    cJ
    wcel
    #
    @17
    @13
    @4
    @3
    @2
    cz
    @4
    @2
    cz
    elpwi
    sselda
    #
    zcnd
    #
    @14
    cc
    cxmt
    cfv
    wcel
    #
    @20
    c1
    cxr
    wcel
    #
    @21
    cnxmet
    c1
    crp
    wcel
    #
    @25
    1rp
    c1
    rpxr
    ax-mp
    #
    @14
    @4
    c1
    cJ
    cc
    cJ
    recld2.1
    cnfldtopn
    blopn
    mp3an13
    cJ
    ctop
    wcel
    #
    cz
    cvv
    wcel
    #
    @21
    @17
    cJ
    recld2.1
    cnfldtop
    #
    zex
    @15
    cz
    cJ
    ctop
    cvv
    elrestr
    mp3an12
    3syl
    @13
    @15
    cz
    @4
    @13
    @20
    @4
    @15
    wcel
    #
    @23
    @24
    @20
    @26
    @31
    cnxmet
    1rp
    @14
    @4
    c1
    cc
    blcntr
    mp3an13
    syl
    @22
    elind
    @13
    vz
    @16
    @2
    @13
    @5
    @16
    wcel
    #
    @5
    @2
    wcel
    @13
    @32
    wa
    #
    @4
    @5
    @2
    @33
    @4
    @5
    @13
    @20
    @32
    @23
    adantr
    #
    @33
    @5
    @33
    @16
    cz
    @5
    @15
    cz
    inss2
    @13
    @32
    simpr
    #
    sseldi
    #
    zcnd
    #
    @33
    @4
    @5
    cmin
    co
    #
    @33
    @38
    @33
    @4
    @5
    @13
    @4
    cz
    wcel
    @32
    @22
    adantr
    @36
    zsubcld
    #
    zcnd
    @33
    @38
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @40
    cc0
    wceq
    #
    @33
    @4
    @5
    @14
    co
    #
    @40
    c1
    clt
    @33
    @20
    @5
    cc
    wcel
    #
    @43
    @40
    wceq
    @34
    @37
    @4
    @5
    @14
    @14
    eqid
    cnmetdval
    syl2anc
    @33
    @5
    @15
    wcel
    #
    @43
    c1
    clt
    wbr
    #
    @33
    @16
    @15
    @5
    @15
    cz
    inss1
    @35
    sseldi
    @33
    @20
    @44
    @45
    @46
    wb
    #
    @34
    @37
    @24
    @25
    @20
    @44
    wa
    @47
    cnxmet
    @27
    @5
    @14
    @4
    c1
    cc
    elbl2
    mpanl12
    syl2anc
    mpbid
    eqbrtrrd
    @33
    @38
    cz
    wcel
    @40
    cn0
    wcel
    @41
    @42
    wb
    @39
    @38
    nn0abscl
    @40
    nn0lt10b
    3syl
    mpbid
    abs00d
    subeq0d
    @3
    @12
    @32
    simplr
    eqeltrrd
    ex
    ssrdv
    @8
    @18
    @19
    wa
    vz
    @16
    @0
    @5
    @16
    wceq
    @6
    @18
    @7
    @19
    @5
    @16
    @4
    eleq2
    @5
    @16
    @2
    sseq1
    anbi12d
    rspcev
    syl12anc
    ralrimiva
    @0
    ctop
    wcel
    #
    @11
    @10
    wb
    @28
    @29
    @48
    @30
    zex
    cz
    cJ
    cvv
    resttop
    mp2an
    vy
    vz
    @2
    @0
    eltop2
    ax-mp
    sylibr
    ssriv
    eqssi
end
