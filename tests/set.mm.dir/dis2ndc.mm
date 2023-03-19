include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "c2ndc.mm"
include "reldom.mm"
include "brrelexi.mm"
include "pwexr.mm"
include "cv.mm"
include "csn.mm"
include "cmpt.mm"
include "crn.mm"
include "cen.mm"
include "wb.mm"
include "wf1o.mm"
include "elex.mm"
include "wf1.mm"
include "snex.mm"
include "2a1i.mm"
include "wceq.mm"
include "wa.mm"
include "vex.mm"
include "sneqr.mm"
include "sneq.mm"
include "impbii.mm"
include "dom2lem.mm"
include "f1f1orn.mm"
include "syl.mm"
include "f1oeng.mm"
include "syl2anc.mm"
include "domen1.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "wss.mm"
include "wel.mm"
include "wrex.mm"
include "wral.mm"
include "distop.mm"
include "wf.mm"
include "simpr.mm"
include "snelpw.mm"
include "sylib.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "sseldd.mm"
include "eqidd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "vsnid.mm"
include "a1i.mm"
include "snssd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "ralrimivva.mm"
include "basgen2.mm"
include "syl3anc.mm"
include "adantr.mm"
include "ctb.mm"
include "eqeltrd.mm"
include "tgclb.mm"
include "2ndci.mm"
include "sylan.mm"
include "eqeltrrd.mm"
include "is2ndc.mm"
include "simplrr.mm"
include "eleqtrrd.mm"
include "tg2.mm"
include "sylancl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "eqssd.mm"
include "simprl.mm"
include "rexlimddv.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "domtr.mm"
include "ex.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "imp.mm"
include "impbida.mm"
include "bitrd.mm"
include "pm5.21nii.mm"

theorem dis2ndc
  let cX: class X
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( X ~<_ _om <-> ~P X e. 2ndc )

  proof
    cX
    com
    cdom
    wbr
    #
    cX
    cvv
    wcel
    #
    cX
    cpw
    #
    c2ndc
    wcel
    #
    cX
    com
    cdom
    reldom
    brrelexi
    cX
    c2ndc
    pwexr
    @1
    @0
    vx
    cX
    vx
    cv
    #
    csn
    #
    cmpt
    #
    crn
    #
    com
    cdom
    wbr
    #
    @3
    @1
    cX
    @7
    cen
    wbr
    #
    @0
    @8
    wb
    @1
    @1
    cX
    @7
    @6
    wf1o
    #
    @9
    cX
    cvv
    elex
    @1
    cX
    cvv
    @6
    wf1
    @10
    @1
    vx
    vy
    cX
    cvv
    @5
    vy
    cv
    #
    csn
    #
    @5
    cvv
    wcel
    @1
    @4
    cX
    wcel
    #
    @4
    snex
    2a1i
    @5
    @12
    wceq
    #
    @4
    @11
    wceq
    #
    wb
    @1
    @13
    @11
    cX
    wcel
    wa
    @14
    @15
    @4
    @11
    vx
    vex
    #
    sneqr
    @4
    @11
    sneq
    impbii
    2a1i
    dom2lem
    cX
    cvv
    @6
    f1f1orn
    syl
    cX
    @7
    cvv
    @6
    f1oeng
    syl2anc
    cX
    @7
    com
    domen1
    syl
    @1
    @8
    @3
    @1
    @8
    wa
    @7
    ctg
    cfv
    #
    @2
    c2ndc
    @1
    @17
    @2
    wceq
    #
    @8
    @1
    @2
    ctop
    wcel
    @7
    @2
    wss
    #
    vz
    vw
    wel
    #
    vw
    cv
    #
    @11
    wss
    #
    wa
    #
    vw
    @7
    wrex
    #
    vz
    @11
    wral
    vy
    @2
    wral
    @18
    cX
    cvv
    distop
    #
    @1
    cX
    @2
    @6
    wf
    @19
    @1
    vx
    cX
    @5
    @2
    @6
    @1
    @13
    wa
    @13
    @5
    @2
    wcel
    #
    @1
    @13
    simpr
    @4
    cX
    @16
    snelpw
    #
    sylib
    @6
    eqid
    #
    fmptd
    cX
    @2
    @6
    frn
    syl
    @1
    @24
    vy
    vz
    @2
    @11
    @1
    @11
    @2
    wcel
    #
    vz
    vy
    wel
    #
    wa
    wa
    #
    vz
    cv
    #
    csn
    #
    @7
    wcel
    #
    @32
    @33
    wcel
    #
    @33
    @11
    wss
    #
    @24
    @31
    @33
    @5
    wceq
    #
    vx
    cX
    wrex
    #
    @34
    @31
    @32
    cX
    wcel
    @33
    @33
    wceq
    #
    @38
    @31
    @11
    cX
    @32
    @29
    @11
    cX
    wss
    @1
    @30
    @11
    cX
    elpwi
    ad2antrl
    @1
    @29
    @30
    simprr
    #
    sseldd
    @31
    @33
    eqidd
    @37
    @39
    vx
    @32
    cX
    @4
    @32
    wceq
    @5
    @33
    @33
    @4
    @32
    sneq
    eqeq2d
    rspcev
    syl2anc
    @33
    cvv
    wcel
    @34
    @38
    wb
    @32
    snex
    vx
    cX
    @5
    @33
    @6
    cvv
    @28
    elrnmpt
    ax-mp
    sylibr
    @35
    @31
    vz
    vsnid
    a1i
    @31
    @32
    @11
    @40
    snssd
    @23
    @35
    @36
    wa
    vw
    @33
    @7
    @21
    @33
    wceq
    @20
    @35
    @22
    @36
    @21
    @33
    @32
    eleq2
    @21
    @33
    @11
    sseq1
    anbi12d
    rspcev
    syl12anc
    ralrimivva
    vy
    vz
    vw
    @7
    @2
    basgen2
    syl3anc
    #
    adantr
    @1
    @7
    ctb
    wcel
    #
    @8
    @17
    c2ndc
    wcel
    @1
    @17
    ctop
    wcel
    @42
    @1
    @17
    @2
    ctop
    @41
    @25
    eqeltrd
    @7
    tgclb
    sylibr
    @7
    2ndci
    sylan
    eqeltrrd
    @1
    @3
    @8
    @3
    vb
    cv
    #
    com
    cdom
    wbr
    #
    @43
    ctg
    cfv
    #
    @2
    wceq
    #
    wa
    #
    vb
    ctb
    wrex
    @1
    @8
    vb
    @2
    is2ndc
    @1
    @47
    @8
    vb
    ctb
    @1
    @43
    ctb
    wcel
    wa
    #
    @47
    @8
    @48
    @47
    wa
    #
    @7
    @43
    cdom
    wbr
    #
    @44
    @8
    @43
    cvv
    wcel
    @49
    @7
    @43
    wss
    #
    @50
    vb
    vex
    @49
    cX
    @43
    @6
    wf
    @51
    @49
    vx
    cX
    @5
    @43
    @6
    @49
    @13
    wa
    #
    vx
    vy
    wel
    #
    @11
    @5
    wss
    #
    wa
    #
    @5
    @43
    wcel
    vy
    @43
    @52
    @5
    @45
    wcel
    @4
    @5
    wcel
    @55
    vy
    @43
    wrex
    @52
    @5
    @2
    @45
    @52
    @13
    @26
    @49
    @13
    simpr
    @27
    sylib
    @48
    @44
    @46
    @13
    simplrr
    eleqtrrd
    vx
    vsnid
    vy
    @5
    @43
    @4
    tg2
    sylancl
    @52
    vy
    vb
    wel
    #
    @55
    wa
    wa
    #
    @5
    @11
    @43
    @57
    @5
    @11
    @57
    @4
    @11
    @52
    @56
    @53
    @54
    simprrl
    snssd
    @52
    @56
    @53
    @54
    simprrr
    eqssd
    @52
    @56
    @55
    simprl
    eqeltrd
    rexlimddv
    @28
    fmptd
    cX
    @43
    @6
    frn
    syl
    @7
    @43
    cvv
    ssdomg
    mpsyl
    @48
    @44
    @46
    simprl
    @7
    @43
    com
    domtr
    syl2anc
    ex
    rexlimdva
    syl5bi
    imp
    impbida
    bitrd
    pm5.21nii
end
