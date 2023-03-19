include "cxp.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "cwdom.mm"
include "cdom.mm"
include "wo.mm"
include "ensym.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "c1st.mm"
include "cres.mm"
include "ccom.mm"
include "cima.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "ssdif0.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "dmxpid.mm"
include "crn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "dmexg.mm"
include "syl5eqelr.mm"
include "imassrn.mm"
include "wf.mm"
include "f1stres.mm"
include "f1of.mm"
include "fco.mm"
include "sylancr.mm"
include "frn.mm"
include "syl5ss.mm"
include "ssexd.mm"
include "adantr.mm"
include "simpr.mm"
include "ssdomg.mm"
include "sylc.mm"
include "domwdom.mm"
include "wfun.mm"
include "ffun.mm"
include "ssun1.mm"
include "f1odm.mm"
include "dmex.mm"
include "ssexg.mm"
include "wdomima2g.mm"
include "syl3anc.mm"
include "wdomtr.mm"
include "syl2anc.mm"
include "orcd.mm"
include "ex.mm"
include "syl5bir.mm"
include "wne.mm"
include "n0.mm"
include "ccnv.mm"
include "csn.mm"
include "ssun2.mm"
include "cfv.mm"
include "wb.mm"
include "wfn.mm"
include "f1ofn.mm"
include "elpreima.mm"
include "wn.mm"
include "wi.mm"
include "elun.mm"
include "df-or.mm"
include "bitri.mm"
include "eldifn.mm"
include "ad2antlr.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "sseldi.mm"
include "fvco3.mm"
include "eldifi.mm"
include "adantl.mm"
include "snssd.mm"
include "xpss1.mm"
include "simprl.mm"
include "sseldd.mm"
include "fvres.mm"
include "xp1st.mm"
include "eqeltrd.mm"
include "elsni.mm"
include "eqtrd.mm"
include "ffn.mm"
include "a1i.mm"
include "fnfvima.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "mtod.mm"
include "imim1d.mm"
include "syl5bi.mm"
include "impd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "wf1.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "snex.mm"
include "xpexg.mm"
include "f1imaen2g.mm"
include "syl22anc.mm"
include "xpsnen2g.mm"
include "entr.mm"
include "domen1.mm"
include "mpbid.mm"
include "olcd.mm"
include "exlimdv.mm"
include "pm2.61dne.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem unxpwdom2
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A X. A ) ~~ ( B u. C ) -> ( A ~<_* B \/ A ~<_ C ) )

  proof
    cA
    cA
    cxp
    #
    cB
    cC
    cun
    #
    cen
    wbr
    @1
    @0
    cen
    wbr
    #
    cA
    cB
    cwdom
    wbr
    #
    cA
    cC
    cdom
    wbr
    #
    wo
    #
    @0
    @1
    ensym
    @2
    @1
    @0
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @5
    @1
    @0
    vf
    bren
    @7
    @5
    vf
    @7
    @5
    cA
    c1st
    @0
    cres
    #
    @6
    ccom
    #
    cB
    cima
    #
    cdif
    #
    c0
    @11
    c0
    wceq
    cA
    @10
    wss
    #
    @7
    @5
    cA
    @10
    ssdif0
    @7
    @12
    @5
    @7
    @12
    wa
    #
    @3
    @4
    @13
    cA
    @10
    cwdom
    wbr
    #
    @10
    cB
    cwdom
    wbr
    #
    @3
    @13
    cA
    @10
    cdom
    wbr
    #
    @14
    @13
    @10
    cvv
    wcel
    #
    @12
    @16
    @7
    @17
    @12
    @7
    @10
    cA
    cvv
    @7
    cA
    @0
    cdm
    #
    cvv
    cA
    dmxpid
    @7
    @0
    cvv
    wcel
    @18
    cvv
    wcel
    @7
    @0
    @6
    crn
    #
    cvv
    @7
    @1
    @0
    @6
    wfo
    @19
    @0
    wceq
    @1
    @0
    @6
    f1ofo
    @1
    @0
    @6
    forn
    syl
    @6
    vf
    vex
    #
    rnex
    syl6eqelr
    @0
    cvv
    dmexg
    syl
    syl5eqelr
    #
    @7
    @10
    @9
    crn
    #
    cA
    @9
    cB
    imassrn
    @7
    @1
    cA
    @9
    wf
    #
    @22
    cA
    wss
    @7
    @0
    cA
    @8
    wf
    @1
    @0
    @6
    wf
    #
    @23
    cA
    cA
    f1stres
    @1
    @0
    @6
    f1of
    #
    @1
    @0
    cA
    @8
    @6
    fco
    sylancr
    #
    @1
    cA
    @9
    frn
    syl
    syl5ss
    ssexd
    #
    adantr
    @7
    @12
    simpr
    cA
    @10
    cvv
    ssdomg
    sylc
    cA
    @10
    domwdom
    syl
    @7
    @15
    @12
    @7
    @9
    wfun
    #
    cB
    cvv
    wcel
    #
    @17
    @15
    @7
    @23
    @28
    @26
    @1
    cA
    @9
    ffun
    syl
    @7
    cB
    @1
    wss
    #
    @1
    cvv
    wcel
    #
    @29
    cB
    cC
    ssun1
    #
    @7
    @1
    @6
    cdm
    cvv
    @1
    @0
    @6
    f1odm
    @6
    @20
    dmex
    syl6eqelr
    #
    cB
    @1
    cvv
    ssexg
    sylancr
    @27
    cB
    @9
    cvv
    cvv
    wdomima2g
    syl3anc
    adantr
    cA
    @10
    cB
    wdomtr
    syl2anc
    orcd
    ex
    syl5bir
    @11
    c0
    wne
    vx
    cv
    #
    @11
    wcel
    #
    vx
    wex
    @7
    @5
    vx
    @11
    n0
    @7
    @35
    @5
    vx
    @7
    @35
    @5
    @7
    @35
    wa
    #
    @4
    @3
    @36
    @6
    ccnv
    #
    @34
    csn
    #
    cA
    cxp
    #
    cima
    #
    cC
    cdom
    wbr
    #
    @4
    @36
    cC
    cvv
    wcel
    #
    @40
    cC
    wss
    @41
    @7
    @42
    @35
    @7
    cC
    @1
    wss
    @31
    @42
    cC
    cB
    ssun2
    @33
    cC
    @1
    cvv
    ssexg
    sylancr
    adantr
    @36
    vy
    @40
    cC
    @36
    vy
    cv
    #
    @40
    wcel
    #
    @43
    @1
    wcel
    #
    @43
    @6
    cfv
    #
    @39
    wcel
    #
    wa
    #
    @43
    cC
    wcel
    #
    @7
    @44
    @48
    wb
    #
    @35
    @7
    @6
    @1
    wfn
    @50
    @1
    @0
    @6
    f1ofn
    @1
    @43
    @39
    @6
    elpreima
    syl
    adantr
    @36
    @45
    @47
    @49
    @45
    @43
    cB
    wcel
    #
    wn
    #
    @49
    wi
    #
    @36
    @47
    @49
    wi
    @45
    @51
    @49
    wo
    @53
    @43
    cB
    cC
    elun
    @51
    @49
    df-or
    bitri
    @36
    @47
    @52
    @49
    @36
    @47
    @52
    @36
    @47
    wa
    @51
    @34
    @10
    wcel
    #
    @35
    @54
    wn
    @7
    @47
    @34
    cA
    @10
    eldifn
    ad2antlr
    @36
    @47
    @51
    @54
    @36
    @47
    @51
    wa
    #
    wa
    #
    @43
    @9
    cfv
    #
    @34
    @10
    @56
    @57
    @46
    @8
    cfv
    #
    @34
    @56
    @24
    @45
    @57
    @58
    wceq
    @7
    @24
    @35
    @55
    @25
    ad2antrr
    @56
    cB
    @1
    @43
    @32
    @36
    @47
    @51
    simprr
    #
    sseldi
    @1
    @0
    @43
    @8
    @6
    fvco3
    syl2anc
    @56
    @58
    @38
    wcel
    @58
    @34
    wceq
    @56
    @58
    @46
    c1st
    cfv
    #
    @38
    @56
    @46
    @0
    wcel
    @58
    @60
    wceq
    @56
    @39
    @0
    @46
    @36
    @39
    @0
    wss
    #
    @55
    @36
    @38
    cA
    wss
    @61
    @36
    @34
    cA
    @35
    @34
    cA
    wcel
    @7
    @34
    cA
    @10
    eldifi
    adantl
    snssd
    @38
    cA
    cA
    xpss1
    syl
    #
    adantr
    @36
    @47
    @51
    simprl
    #
    sseldd
    @46
    @0
    c1st
    fvres
    syl
    @56
    @47
    @60
    @38
    wcel
    @63
    @46
    @38
    cA
    xp1st
    syl
    eqeltrd
    @58
    @34
    elsni
    syl
    eqtrd
    @56
    @9
    @1
    wfn
    #
    @30
    @51
    @57
    @10
    wcel
    @7
    @64
    @35
    @55
    @7
    @23
    @64
    @26
    @1
    cA
    @9
    ffn
    syl
    ad2antrr
    @30
    @56
    @32
    a1i
    @59
    @1
    cB
    @9
    @43
    fnfvima
    syl3anc
    eqeltrrd
    expr
    mtod
    ex
    imim1d
    syl5bi
    impd
    sylbid
    ssrdv
    @40
    cC
    cvv
    ssdomg
    sylc
    @36
    @40
    cA
    cen
    wbr
    #
    @41
    @4
    wb
    @36
    @40
    @39
    cen
    wbr
    #
    @39
    cA
    cen
    wbr
    #
    @65
    @36
    @0
    @1
    @37
    wf1
    #
    @31
    @61
    @39
    cvv
    wcel
    #
    @66
    @7
    @68
    @35
    @7
    @0
    @1
    @37
    wf1o
    @68
    @1
    @0
    @6
    f1ocnv
    @0
    @1
    @37
    f1of1
    syl
    adantr
    @7
    @31
    @35
    @33
    adantr
    @62
    @36
    @38
    cvv
    wcel
    cA
    cvv
    wcel
    #
    @69
    @34
    snex
    @7
    @70
    @35
    @21
    adantr
    #
    @38
    cA
    cvv
    cvv
    xpexg
    sylancr
    @0
    @1
    @39
    @37
    cvv
    f1imaen2g
    syl22anc
    @36
    @34
    cvv
    wcel
    @70
    @67
    vx
    vex
    @71
    @34
    cA
    cvv
    cvv
    xpsnen2g
    sylancr
    @40
    @39
    cA
    entr
    syl2anc
    @40
    cA
    cC
    domen1
    syl
    mpbid
    olcd
    ex
    exlimdv
    syl5bi
    pm2.61dne
    exlimiv
    sylbi
    syl
end
