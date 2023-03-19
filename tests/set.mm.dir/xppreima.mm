include "wfun.mm"
include "crn.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cv.mm"
include "c1st.mm"
include "ccom.mm"
include "wcel.mm"
include "c2nd.mm"
include "cdm.mm"
include "crab.mm"
include "cin.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "funfn.mm"
include "fncnvima2.mm"
include "sylbi.mm"
include "adantr.mm"
include "cop.mm"
include "wb.mm"
include "fvco.mm"
include "opeq12d.mm"
include "eqeq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "elxp6.mm"
include "syl6rbbr.mm"
include "adantlr.mm"
include "opfv.mm"
include "biantrurd.mm"
include "wfo.mm"
include "fo1st.mm"
include "fofun.mm"
include "ax-mp.mm"
include "funco.mm"
include "mpan.mm"
include "ssv.mm"
include "wf.mm"
include "fof.mm"
include "fdm.mm"
include "mp2b.mm"
include "sseqtr4i.mm"
include "ssid.mm"
include "funimass3.mm"
include "mpan2.mm"
include "mpbii.mm"
include "sselda.mm"
include "dmco.mm"
include "syl6eleqr.mm"
include "fvimacnv.mm"
include "syl2anc.mm"
include "fo2nd.mm"
include "3bitr2d.mm"
include "rabbidva.mm"
include "eqtrd.mm"
include "dfin5.mm"
include "ineq12i.mm"
include "cnvimass.mm"
include "dmcoss.mm"
include "sstri.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "inrab.mm"
include "3eqtr3ri.mm"
include "syl6eq.mm"

theorem xppreima
  let cF: class F
  let cY: class Y
  let cZ: class Z
  let vx: setvar x


  assert |- ( ( Fun F /\ ran F C_ ( _V X. _V ) ) -> ( `' F " ( Y X. Z ) ) = ( ( `' ( 1st o. F ) " Y ) i^i ( `' ( 2nd o. F ) " Z ) ) )

  proof
    cF
    wfun
    #
    cF
    crn
    cvv
    cvv
    cxp
    wss
    #
    wa
    #
    cF
    ccnv
    #
    cY
    cZ
    cxp
    #
    cima
    #
    vx
    cv
    #
    c1st
    cF
    ccom
    #
    ccnv
    cY
    cima
    #
    wcel
    #
    @6
    c2nd
    cF
    ccom
    #
    ccnv
    cZ
    cima
    #
    wcel
    #
    wa
    #
    vx
    cF
    cdm
    #
    crab
    #
    @8
    @11
    cin
    #
    @2
    @5
    @6
    cF
    cfv
    #
    @4
    wcel
    #
    vx
    @14
    crab
    #
    @15
    @0
    @5
    @19
    wceq
    #
    @1
    @0
    cF
    @14
    wfn
    @20
    cF
    funfn
    vx
    @14
    @4
    cF
    fncnvima2
    sylbi
    adantr
    @2
    @18
    @13
    vx
    @14
    @2
    @6
    @14
    wcel
    #
    wa
    #
    @18
    @17
    @6
    @7
    cfv
    #
    @6
    @10
    cfv
    #
    cop
    #
    wceq
    #
    @23
    cY
    wcel
    #
    @24
    cZ
    wcel
    #
    wa
    #
    wa
    #
    @29
    @13
    @0
    @21
    @18
    @30
    wb
    @1
    @0
    @21
    wa
    #
    @30
    @17
    @17
    c1st
    cfv
    #
    @17
    c2nd
    cfv
    #
    cop
    #
    wceq
    #
    @32
    cY
    wcel
    #
    @33
    cZ
    wcel
    #
    wa
    #
    wa
    @18
    @31
    @26
    @35
    @29
    @38
    @31
    @25
    @34
    @17
    @31
    @23
    @32
    @24
    @33
    @6
    c1st
    cF
    fvco
    #
    @6
    c2nd
    cF
    fvco
    #
    opeq12d
    eqeq2d
    @31
    @27
    @36
    @28
    @37
    @31
    @23
    @32
    cY
    @39
    eleq1d
    @31
    @24
    @33
    cZ
    @40
    eleq1d
    anbi12d
    anbi12d
    @17
    cY
    cZ
    elxp6
    syl6rbbr
    adantlr
    @22
    @26
    @29
    vx
    cF
    opfv
    biantrurd
    @0
    @21
    @29
    @13
    wb
    @1
    @31
    @27
    @9
    @28
    @12
    @31
    @7
    wfun
    #
    @6
    @7
    cdm
    #
    wcel
    @27
    @9
    wb
    @0
    @41
    @21
    c1st
    wfun
    #
    @0
    @41
    cvv
    cvv
    c1st
    wfo
    #
    @43
    fo1st
    cvv
    cvv
    c1st
    fofun
    ax-mp
    c1st
    cF
    funco
    mpan
    adantr
    @31
    @6
    @3
    c1st
    cdm
    #
    cima
    #
    @42
    @0
    @14
    @46
    @6
    @0
    cF
    @14
    cima
    #
    @45
    wss
    #
    @14
    @46
    wss
    #
    @47
    cvv
    @45
    @47
    ssv
    #
    @44
    cvv
    cvv
    c1st
    wf
    @45
    cvv
    wceq
    fo1st
    cvv
    cvv
    c1st
    fof
    cvv
    cvv
    c1st
    fdm
    mp2b
    sseqtr4i
    @0
    @14
    @14
    wss
    #
    @48
    @49
    wb
    @14
    ssid
    #
    @14
    @45
    cF
    funimass3
    mpan2
    mpbii
    sselda
    c1st
    cF
    dmco
    syl6eleqr
    @6
    cY
    @7
    fvimacnv
    syl2anc
    @31
    @10
    wfun
    #
    @6
    @10
    cdm
    #
    wcel
    @28
    @12
    wb
    @0
    @53
    @21
    c2nd
    wfun
    #
    @0
    @53
    cvv
    cvv
    c2nd
    wfo
    #
    @55
    fo2nd
    cvv
    cvv
    c2nd
    fofun
    ax-mp
    c2nd
    cF
    funco
    mpan
    adantr
    @31
    @6
    @3
    c2nd
    cdm
    #
    cima
    #
    @54
    @0
    @14
    @58
    @6
    @0
    @47
    @57
    wss
    #
    @14
    @58
    wss
    #
    @47
    cvv
    @57
    @50
    @56
    cvv
    cvv
    c2nd
    wf
    @57
    cvv
    wceq
    fo2nd
    cvv
    cvv
    c2nd
    fof
    cvv
    cvv
    c2nd
    fdm
    mp2b
    sseqtr4i
    @0
    @51
    @59
    @60
    wb
    @52
    @14
    @57
    cF
    funimass3
    mpan2
    mpbii
    sselda
    c2nd
    cF
    dmco
    syl6eleqr
    @6
    cZ
    @10
    fvimacnv
    syl2anc
    anbi12d
    adantlr
    3bitr2d
    rabbidva
    eqtrd
    @14
    @8
    cin
    #
    @14
    @11
    cin
    #
    cin
    @9
    vx
    @14
    crab
    #
    @12
    vx
    @14
    crab
    #
    cin
    @16
    @15
    @61
    @63
    @62
    @64
    vx
    @14
    @8
    dfin5
    vx
    @14
    @11
    dfin5
    ineq12i
    @61
    @8
    @62
    @11
    @8
    @14
    wss
    @61
    @8
    wceq
    @8
    @42
    @14
    @7
    cY
    cnvimass
    c1st
    cF
    dmcoss
    sstri
    @8
    @14
    sseqin2
    mpbi
    @11
    @14
    wss
    @62
    @11
    wceq
    @11
    @54
    @14
    @10
    cZ
    cnvimass
    c2nd
    cF
    dmcoss
    sstri
    @11
    @14
    sseqin2
    mpbi
    ineq12i
    @9
    @12
    vx
    @14
    inrab
    3eqtr3ri
    syl6eq
end
