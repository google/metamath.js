include "ccrd.mm"
include "cr1.mm"
include "ccom.mm"
include "ccnv.mm"
include "cdm.mm"
include "cima.mm"
include "con0.mm"
include "wf.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "cab.mm"
include "cardf2.mm"
include "ffun.mm"
include "ax-mp.mm"
include "r1fnon.mm"
include "fnfun.mm"
include "funco.mm"
include "mp2an.mm"
include "funfn.mm"
include "mpbi.mm"
include "cres.mm"
include "rnco.mm"
include "resss.mm"
include "rnss.mm"
include "frn.mm"
include "sstri.mm"
include "eqsstri.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "dmco.mm"
include "feq2i.mm"
include "word.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "wb.mm"
include "elpreima.mm"
include "simplbi.mm"
include "onelon.mm"
include "sylan.mm"
include "simprbi.mm"
include "adantr.mm"
include "r1ord2.mm"
include "imp.mm"
include "ssnum.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "rgen2.mm"
include "dftr5.mm"
include "mpbir.mm"
include "cnvimass.mm"
include "cvv.mm"
include "dffn2.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "epweon.mm"
include "wess.mm"
include "mp2.mm"
include "df-ord.mm"
include "wi.mm"
include "csdm.mm"
include "r1sdom.mm"
include "cardsdom2.mm"
include "mpbird.mm"
include "wceq.mm"
include "fvco2.mm"
include "sylancr.mm"
include "3eltr4d.mm"
include "ex.mm"
include "adantl.mm"
include "issmo.mm"

theorem smobeth
  let vx: setvar x
  let vy: setvar y


  assert |- Smo ( card o. R1 )

  proof
    vy
    vx
    ccrd
    cr1
    ccom
    #
    cr1
    ccnv
    ccrd
    cdm
    #
    cima
    #
    @0
    cdm
    #
    con0
    @0
    wf
    #
    @2
    con0
    @0
    wf
    @4
    @0
    @3
    wfn
    #
    @0
    crn
    #
    con0
    wss
    @0
    wfun
    #
    @5
    ccrd
    wfun
    #
    cr1
    wfun
    #
    @7
    vy
    cv
    #
    vx
    cv
    #
    cen
    wbr
    vy
    con0
    wrex
    vx
    cab
    #
    con0
    ccrd
    wf
    #
    @8
    vx
    vy
    cardf2
    #
    @12
    con0
    ccrd
    ffun
    ax-mp
    cr1
    con0
    wfn
    #
    @9
    r1fnon
    con0
    cr1
    fnfun
    ax-mp
    ccrd
    cr1
    funco
    mp2an
    @0
    funfn
    mpbi
    @6
    ccrd
    cr1
    crn
    #
    cres
    #
    crn
    #
    con0
    ccrd
    cr1
    rnco
    @18
    ccrd
    crn
    #
    con0
    @17
    ccrd
    wss
    @18
    @19
    wss
    ccrd
    @16
    resss
    @17
    ccrd
    rnss
    ax-mp
    @13
    @19
    con0
    wss
    @14
    @12
    con0
    ccrd
    frn
    ax-mp
    sstri
    eqsstri
    @3
    con0
    @0
    df-f
    mpbir2an
    @3
    @2
    con0
    @0
    ccrd
    cr1
    dmco
    #
    feq2i
    mpbi
    @2
    word
    @2
    wtr
    #
    @2
    cep
    wwe
    #
    @21
    @10
    @2
    wcel
    #
    vy
    @11
    wral
    vx
    @2
    wral
    @23
    vx
    vy
    @2
    @11
    @11
    @2
    wcel
    #
    @10
    @11
    wcel
    #
    wa
    #
    @10
    con0
    wcel
    #
    @10
    cr1
    cfv
    #
    @1
    wcel
    #
    @23
    @24
    @11
    con0
    wcel
    #
    @25
    @27
    @24
    @30
    @11
    cr1
    cfv
    #
    @1
    wcel
    #
    @15
    @24
    @30
    @32
    wa
    wb
    r1fnon
    con0
    @11
    @1
    cr1
    elpreima
    ax-mp
    #
    simplbi
    #
    @11
    @10
    onelon
    sylan
    #
    @26
    @32
    @28
    @31
    wss
    #
    @29
    @24
    @32
    @25
    @24
    @30
    @32
    @33
    simprbi
    adantr
    #
    @24
    @30
    @25
    @36
    @34
    @30
    @25
    @36
    @10
    @11
    r1ord2
    imp
    sylan
    @31
    @28
    ssnum
    syl2anc
    #
    @15
    @23
    @27
    @29
    wa
    wb
    r1fnon
    con0
    @10
    @1
    cr1
    elpreima
    ax-mp
    sylanbrc
    rgen2
    vx
    vy
    @2
    dftr5
    mpbir
    @2
    con0
    wss
    con0
    cep
    wwe
    @22
    @2
    cr1
    cdm
    con0
    cr1
    @1
    cnvimass
    con0
    cvv
    cr1
    @15
    con0
    cvv
    cr1
    wf
    r1fnon
    con0
    cr1
    dffn2
    mpbi
    fdmi
    sseqtri
    epweon
    @2
    con0
    cep
    wess
    mp2
    @2
    df-ord
    mpbir2an
    @24
    @25
    @10
    @0
    cfv
    #
    @11
    @0
    cfv
    #
    wcel
    #
    wi
    @23
    @24
    @25
    @41
    @26
    @28
    ccrd
    cfv
    #
    @31
    ccrd
    cfv
    #
    @39
    @40
    @26
    @42
    @43
    wcel
    #
    @28
    @31
    csdm
    wbr
    #
    @24
    @30
    @25
    @45
    @34
    @11
    @10
    r1sdom
    sylan
    @26
    @29
    @32
    @44
    @45
    wb
    @38
    @37
    @28
    @31
    cardsdom2
    syl2anc
    mpbird
    @26
    @15
    @27
    @39
    @42
    wceq
    r1fnon
    @35
    con0
    ccrd
    cr1
    @10
    fvco2
    sylancr
    @26
    @15
    @30
    @40
    @43
    wceq
    r1fnon
    @24
    @30
    @25
    @34
    adantr
    con0
    ccrd
    cr1
    @11
    fvco2
    sylancr
    3eltr4d
    ex
    adantl
    @20
    issmo
end
