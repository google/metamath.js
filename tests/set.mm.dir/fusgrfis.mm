include "cfusgr.mm"
include "wcel.mm"
include "cusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "cfn.mm"
include "wa.mm"
include "cedg.mm"
include "eqid.mm"
include "isfusgr.mm"
include "ciedg.mm"
include "cop.mm"
include "usgrop.mm"
include "cv.mm"
include "cid.mm"
include "wnel.mm"
include "crab.mm"
include "cres.mm"
include "fvex.mm"
include "cmpt.mm"
include "cvv.mm"
include "mptresid.mm"
include "mptrabex.mm"
include "eqeltrri.mm"
include "wceq.mm"
include "wb.mm"
include "eleq1.mm"
include "adantl.mm"
include "csn.mm"
include "cdif.mm"
include "vex.mm"
include "opvtxfvi.mm"
include "eqcomi.mm"
include "usgrres1.mm"
include "chash.mm"
include "cc0.mm"
include "pm3.2i.mm"
include "fusgrfisbase.mm"
include "mp3an1.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cn0.mm"
include "w3a.mm"
include "wi.mm"
include "simpl.mm"
include "simprr1.mm"
include "hashclb.mm"
include "biimprd.mm"
include "adantr.mm"
include "com12.mm"
include "syl6bir.mm"
include "3ad2ant2.mm"
include "impcom.mm"
include "opfusgr.mm"
include "mpbir2and.mm"
include "simprr3.mm"
include "3jca.mm"
include "mpan.mm"
include "fusgrfisstep.mm"
include "syl.mm"
include "imp.mm"
include "opfi1ind.mm"
include "sylan.mm"
include "usgredgffibi.mm"
include "mpbird.mm"
include "sylbi.mm"

theorem fusgrfis
  let cG: class G
  let ve: setvar e
  let vf: setvar f
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vv: setvar v
  let vy: setvar y
  let vw: setvar w


  assert |- ( G e. FinUSGraph -> ( Edg ` G ) e. Fin )

  proof
    cG
    cfusgr
    wcel
    cG
    cusgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    wa
    #
    cG
    cedg
    cfv
    #
    cfn
    wcel
    #
    cG
    @1
    @1
    eqid
    isfusgr
    @3
    @5
    cG
    ciedg
    cfv
    #
    cfn
    wcel
    #
    @0
    @1
    @6
    cop
    cusgr
    wcel
    @2
    @7
    cG
    usgrop
    @7
    ve
    cv
    #
    cfn
    wcel
    #
    cid
    vn
    cv
    #
    vp
    cv
    wnel
    #
    vp
    vv
    cv
    #
    @8
    cop
    #
    cedg
    cfv
    #
    crab
    #
    cres
    #
    cfn
    wcel
    #
    vf
    cv
    #
    cfn
    wcel
    #
    vy
    vw
    vv
    ve
    vf
    vn
    @6
    @16
    cusgr
    @1
    cG
    ciedg
    fvex
    vq
    @15
    vq
    cv
    #
    cmpt
    @16
    cvv
    vq
    @15
    mptresid
    @11
    vq
    vp
    @14
    @20
    @13
    cedg
    fvex
    mptrabex
    eqeltrri
    @8
    @6
    wceq
    @9
    @7
    wb
    @12
    @1
    wceq
    @8
    @6
    cfn
    eleq1
    adantl
    @8
    @18
    wceq
    @9
    @19
    wb
    @12
    vw
    cv
    #
    wceq
    @8
    @18
    cfn
    eleq1
    adantl
    @12
    @10
    csn
    cdif
    #
    @16
    cop
    #
    vp
    @14
    @15
    @13
    @10
    @12
    @13
    cvtx
    cfv
    @12
    @8
    @12
    vv
    vex
    #
    ve
    vex
    #
    opvtxfvi
    eqcomi
    @14
    eqid
    @15
    eqid
    @23
    eqid
    usgrres1
    @18
    @16
    wceq
    @19
    @17
    wb
    @21
    @22
    wceq
    @18
    @16
    cfn
    eleq1
    adantl
    @12
    cvv
    wcel
    #
    @8
    cvv
    wcel
    #
    wa
    #
    @13
    cusgr
    wcel
    #
    @12
    chash
    cfv
    #
    cc0
    wceq
    @9
    @26
    @27
    @24
    @25
    pm3.2i
    #
    @8
    @12
    cvv
    cvv
    fusgrfisbase
    mp3an1
    vy
    cv
    c1
    caddc
    co
    #
    cn0
    wcel
    #
    @29
    @30
    @32
    wceq
    #
    @10
    @12
    wcel
    #
    w3a
    #
    wa
    #
    @17
    @9
    @37
    @28
    @13
    cfusgr
    wcel
    #
    @35
    w3a
    #
    @17
    @9
    wi
    @28
    @37
    @39
    @31
    @28
    @37
    wa
    #
    @28
    @38
    @35
    @28
    @37
    simpl
    @40
    @38
    @29
    @12
    cfn
    wcel
    #
    @29
    @34
    @35
    @33
    @28
    simprr1
    @37
    @28
    @41
    @36
    @33
    @28
    @41
    wi
    #
    @34
    @29
    @33
    @42
    wi
    @35
    @34
    @33
    @30
    cn0
    wcel
    #
    @42
    @30
    @32
    cn0
    eleq1
    @28
    @43
    @41
    @26
    @43
    @41
    wi
    @27
    @26
    @41
    @43
    @12
    cvv
    hashclb
    biimprd
    adantr
    com12
    syl6bir
    3ad2ant2
    impcom
    impcom
    @28
    @38
    @29
    @41
    wa
    wb
    @37
    @8
    @12
    cvv
    cvv
    opfusgr
    adantr
    mpbir2and
    @29
    @34
    @35
    @33
    @28
    simprr3
    3jca
    mpan
    @8
    @10
    @12
    cvv
    cvv
    vp
    fusgrfisstep
    syl
    imp
    opfi1ind
    sylan
    @0
    @5
    @7
    wb
    @2
    @4
    cG
    @6
    @6
    eqid
    @4
    eqid
    usgredgffibi
    adantr
    mpbird
    sylbi
end
