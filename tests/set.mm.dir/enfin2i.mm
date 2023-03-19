include "cen.mm"
include "wbr.mm"
include "cfin2.mm"
include "wcel.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cuni.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "wss.mm"
include "elpwi.mm"
include "cima.mm"
include "crab.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "ciun.mm"
include "imauni.mm"
include "vex.mm"
include "imaex.mm"
include "dfiun2.mm"
include "eqtri.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rexrab.mm"
include "eleq1.mm"
include "biimparc.mm"
include "rexlimivw.mm"
include "ccnv.mm"
include "cdm.mm"
include "cnvimass.mm"
include "f1odm.mm"
include "ad3antrrr.mm"
include "syl5sseq.mm"
include "cnvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "wfo.mm"
include "f1ofo.mm"
include "simprl.mm"
include "sselda.mm"
include "elpwid.mm"
include "foimacnv.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "impbid2.mm"
include "syl5bb.mm"
include "abbi1dv.mm"
include "unieqd.mm"
include "syl5eq.mm"
include "simplr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simprrl.mm"
include "n0.mm"
include "sylib.mm"
include "exlimddv.mm"
include "rabn0.mm"
include "wo.mm"
include "elrab.mm"
include "anbi12i.mm"
include "simprrr.mm"
include "adantr.mm"
include "simprlr.mm"
include "sorpssi.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "simprll.mm"
include "f1imass.mm"
include "orbi12d.mm"
include "mpbid.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "sorpss.mm"
include "fin2i.mm"
include "syl22anc.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "expr.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "cvv.mm"
include "relen.mm"
include "brrelex2i.mm"
include "isfin2.mm"
include "sylibrd.mm"

theorem enfin2i
  let cA: class A
  let cB: class B
  let vb: setvar b
  let vc: setvar c
  let vf: setvar f
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cV: class V


  assert |- ( A ~~ B -> ( A e. Fin2 -> B e. Fin2 ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cA
    cfin2
    wcel
    #
    vx
    cv
    #
    c0
    wne
    #
    @2
    crpss
    wor
    #
    wa
    #
    @2
    cuni
    #
    @2
    wcel
    #
    wi
    #
    vx
    cB
    cpw
    #
    cpw
    #
    wral
    #
    cB
    cfin2
    wcel
    #
    @0
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @1
    @11
    wi
    #
    cA
    cB
    vf
    bren
    @14
    @15
    vf
    @14
    @1
    @11
    @14
    @1
    wa
    #
    @8
    vx
    @10
    @2
    @10
    wcel
    @16
    @2
    @9
    wss
    #
    @8
    @2
    @9
    elpwi
    @16
    @17
    @5
    @7
    @16
    @17
    @5
    wa
    #
    wa
    #
    @13
    @13
    vy
    cv
    #
    cima
    #
    @2
    wcel
    #
    vy
    cA
    cpw
    #
    crab
    #
    cuni
    #
    cima
    #
    @6
    @2
    @19
    @26
    vw
    cv
    #
    @13
    vz
    cv
    #
    cima
    #
    wceq
    #
    vz
    @24
    wrex
    #
    vw
    cab
    #
    cuni
    #
    @6
    @26
    vz
    @24
    @29
    ciun
    @33
    vz
    @13
    @24
    imauni
    vz
    vw
    @24
    @29
    @13
    @28
    vf
    vex
    #
    imaex
    dfiun2
    eqtri
    @19
    @32
    @2
    @19
    @31
    vw
    @2
    @31
    @29
    @2
    wcel
    #
    @30
    wa
    #
    vz
    @23
    wrex
    #
    @19
    @27
    @2
    wcel
    #
    @22
    @35
    @30
    vz
    vy
    @23
    @20
    @28
    wceq
    @21
    @29
    @2
    @20
    @28
    @13
    imaeq2
    eleq1d
    #
    rexrab
    @19
    @37
    @38
    @36
    @38
    vz
    @23
    @30
    @38
    @35
    @27
    @29
    @2
    eleq1
    biimparc
    rexlimivw
    @19
    @38
    @37
    @19
    @38
    wa
    #
    @13
    ccnv
    #
    @27
    cima
    #
    @23
    wcel
    #
    @13
    @42
    cima
    #
    @2
    wcel
    #
    @27
    @44
    wceq
    #
    @37
    @40
    @42
    cA
    wss
    @43
    @40
    @13
    cdm
    #
    @42
    cA
    @13
    @27
    cnvimass
    @14
    @47
    cA
    wceq
    @1
    @18
    @38
    cA
    cB
    @13
    f1odm
    ad3antrrr
    syl5sseq
    @42
    cA
    @41
    @27
    @13
    @34
    cnvex
    imaex
    elpw
    sylibr
    #
    @40
    @27
    @44
    @2
    @40
    @44
    @27
    @40
    cA
    cB
    @13
    wfo
    #
    @27
    cB
    wss
    @44
    @27
    wceq
    @14
    @49
    @1
    @18
    @38
    cA
    cB
    @13
    f1ofo
    ad3antrrr
    @40
    @27
    cB
    @19
    @2
    @9
    @27
    @16
    @17
    @5
    simprl
    sselda
    elpwid
    cA
    cB
    @27
    @13
    foimacnv
    syl2anc
    eqcomd
    #
    @19
    @38
    simpr
    eqeltrrd
    #
    @50
    @36
    @45
    @46
    wa
    vz
    @42
    @23
    @28
    @42
    wceq
    #
    @35
    @45
    @30
    @46
    @52
    @29
    @44
    @2
    @28
    @42
    @13
    imaeq2
    #
    eleq1d
    @52
    @29
    @44
    @27
    @53
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    ex
    impbid2
    syl5bb
    abbi1dv
    unieqd
    syl5eq
    @19
    @25
    @24
    wcel
    #
    @26
    @2
    wcel
    #
    @19
    @1
    @24
    @23
    wss
    #
    @24
    c0
    wne
    #
    @24
    crpss
    wor
    #
    @54
    @14
    @1
    @18
    simplr
    @56
    @19
    @22
    vy
    @23
    ssrab2
    a1i
    @19
    @22
    vy
    @23
    wrex
    #
    @57
    @19
    @38
    @59
    vw
    @19
    @3
    @38
    vw
    wex
    @16
    @17
    @3
    @4
    simprrl
    vw
    @2
    n0
    sylib
    @40
    @43
    @45
    @59
    @48
    @51
    @22
    @45
    vy
    @42
    @23
    @20
    @42
    wceq
    @21
    @44
    @2
    @20
    @42
    @13
    imaeq2
    eleq1d
    rspcev
    syl2anc
    exlimddv
    @22
    vy
    @23
    rabn0
    sylibr
    @19
    @28
    @27
    wss
    #
    @27
    @28
    wss
    #
    wo
    #
    vw
    @24
    wral
    vz
    @24
    wral
    @58
    @19
    @62
    vz
    vw
    @24
    @24
    @28
    @24
    wcel
    #
    @27
    @24
    wcel
    #
    wa
    @19
    @28
    @23
    wcel
    #
    @35
    wa
    #
    @27
    @23
    wcel
    #
    @13
    @27
    cima
    #
    @2
    wcel
    #
    wa
    #
    wa
    #
    @62
    @63
    @66
    @64
    @70
    @22
    @35
    vy
    @28
    @23
    @39
    elrab
    @22
    @69
    vy
    @27
    @23
    @20
    @27
    wceq
    @21
    @68
    @2
    @20
    @27
    @13
    imaeq2
    eleq1d
    elrab
    anbi12i
    @19
    @71
    wa
    #
    @29
    @68
    wss
    #
    @68
    @29
    wss
    #
    wo
    #
    @62
    @72
    @4
    @35
    @69
    @75
    @19
    @4
    @71
    @16
    @17
    @3
    @4
    simprrr
    adantr
    @19
    @65
    @35
    @70
    simprlr
    @19
    @66
    @67
    @69
    simprrr
    @2
    @29
    @68
    sorpssi
    syl12anc
    @72
    @73
    @60
    @74
    @61
    @72
    cA
    cB
    @13
    wf1
    #
    @28
    cA
    wss
    #
    @27
    cA
    wss
    #
    @73
    @60
    wb
    @14
    @76
    @1
    @18
    @71
    cA
    cB
    @13
    f1of1
    ad3antrrr
    #
    @72
    @28
    cA
    @19
    @65
    @35
    @70
    simprll
    elpwid
    #
    @72
    @27
    cA
    @19
    @66
    @67
    @69
    simprrl
    elpwid
    #
    cA
    cB
    @28
    @27
    @13
    f1imass
    syl12anc
    @72
    @76
    @78
    @77
    @74
    @61
    wb
    @79
    @81
    @80
    cA
    cB
    @27
    @28
    @13
    f1imass
    syl12anc
    orbi12d
    mpbid
    sylan2b
    ralrimivva
    vz
    vw
    @24
    sorpss
    sylibr
    cA
    @24
    fin2i
    syl22anc
    @54
    @25
    @23
    wcel
    @55
    @35
    @55
    vz
    @25
    @23
    @24
    @28
    @25
    wceq
    @29
    @26
    @2
    @28
    @25
    @13
    imaeq2
    eleq1d
    @22
    @35
    vy
    vz
    @23
    @39
    cbvrabv
    elrab2
    simprbi
    syl
    eqeltrrd
    expr
    sylan2
    ralrimiva
    ex
    exlimiv
    sylbi
    @0
    cB
    cvv
    wcel
    @12
    @11
    wb
    cA
    cB
    cen
    relen
    brrelex2i
    vx
    cB
    cvv
    isfin2
    syl
    sylibrd
end
