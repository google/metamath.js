include "cfn.mm"
include "wcel.mm"
include "wpss.mm"
include "csdm.mm"
include "wbr.mm"
include "cv.mm"
include "cen.mm"
include "com.mm"
include "wrex.mm"
include "wi.mm"
include "isfi.mm"
include "wa.mm"
include "cdom.mm"
include "wn.mm"
include "cvv.mm"
include "wss.mm"
include "relen.mm"
include "brrelexi.mm"
include "pssss.mm"
include "ssdomg.mm"
include "imp.mm"
include "syl2an.mm"
include "adantll.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "cima.mm"
include "imass2.mm"
include "syl.mm"
include "adantl.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "pssnel.mm"
include "eldif.mm"
include "cfv.mm"
include "wfn.mm"
include "f1ofn.mm"
include "difss.mm"
include "fnfvima.mm"
include "3expia.mm"
include "sylancl.mm"
include "ccnv.mm"
include "wfun.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "imadif.mm"
include "eleq2d.mm"
include "sylibd.mm"
include "n0i.mm"
include "syl6.mm"
include "syl5bir.mm"
include "exlimdv.mm"
include "sylan2.mm"
include "ssdif0.mm"
include "sylnibr.mm"
include "dfpss3.mm"
include "sylanbrc.mm"
include "wb.mm"
include "cdm.mm"
include "crn.mm"
include "imadmrn.mm"
include "f1odm.mm"
include "imaeq2d.mm"
include "f1ofo.mm"
include "forn.mm"
include "3eqtr3a.mm"
include "psseq2d.mm"
include "adantr.mm"
include "mpbid.mm"
include "php.mm"
include "cres.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1ores.mm"
include "vex.mm"
include "resex.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "sylibr.mm"
include "entr.mm"
include "expcom.mm"
include "mtod.mm"
include "exp32.mm"
include "syl5bi.mm"
include "imp31.mm"
include "ex.mm"
include "ensym.mm"
include "syl6com.mm"
include "ad2antlr.mm"
include "brsdom.mm"
include "exp31.mm"
include "rexlimiv.mm"
include "sylbi.mm"

theorem php3
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. Fin /\ B C. A ) -> B ~< A )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wpss
    #
    cB
    cA
    csdm
    wbr
    #
    @0
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    @1
    @2
    wi
    #
    vx
    cA
    isfi
    @4
    @5
    vx
    com
    @3
    com
    wcel
    #
    @4
    @1
    @2
    @6
    @4
    wa
    @1
    wa
    #
    cB
    cA
    cdom
    wbr
    #
    cB
    cA
    cen
    wbr
    #
    wn
    @2
    @4
    @1
    @8
    @6
    @4
    cA
    cvv
    wcel
    #
    cB
    cA
    wss
    #
    @8
    @1
    cA
    @3
    cen
    relen
    brrelexi
    cB
    cA
    pssss
    #
    @10
    @11
    @8
    cB
    cA
    cvv
    ssdomg
    imp
    syl2an
    adantll
    @7
    @9
    @3
    cB
    cen
    wbr
    #
    @6
    @4
    @1
    @13
    wn
    #
    @4
    cA
    @3
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    @6
    @1
    @14
    wi
    #
    cA
    @3
    vf
    bren
    @6
    @16
    @17
    vf
    @6
    @16
    @1
    @14
    @6
    @16
    @1
    wa
    #
    wa
    @13
    @3
    @15
    cB
    cima
    #
    cen
    wbr
    #
    @18
    @6
    @19
    @3
    wpss
    #
    @20
    wn
    @18
    @19
    @15
    cA
    cima
    #
    wpss
    #
    @21
    @18
    @19
    @22
    wss
    #
    @22
    @19
    wss
    #
    wn
    @23
    @1
    @24
    @16
    @1
    @11
    @24
    @12
    cB
    cA
    @15
    imass2
    syl
    adantl
    @18
    @22
    @19
    cdif
    #
    c0
    wceq
    #
    @25
    @1
    @16
    vy
    cv
    #
    cA
    wcel
    @28
    cB
    wcel
    wn
    wa
    #
    vy
    wex
    #
    @27
    wn
    #
    vy
    cB
    cA
    pssnel
    @16
    @30
    @31
    @16
    @29
    @31
    vy
    @29
    @28
    cA
    cB
    cdif
    #
    wcel
    #
    @16
    @31
    @28
    cA
    cB
    eldif
    @16
    @33
    @28
    @15
    cfv
    #
    @26
    wcel
    #
    @31
    @16
    @33
    @34
    @15
    @32
    cima
    #
    wcel
    #
    @35
    @16
    @15
    cA
    wfn
    #
    @32
    cA
    wss
    #
    @33
    @37
    wi
    cA
    @3
    @15
    f1ofn
    cA
    cB
    difss
    @38
    @39
    @33
    @37
    cA
    @32
    @15
    @28
    fnfvima
    3expia
    sylancl
    @16
    @36
    @26
    @34
    @16
    @15
    ccnv
    wfun
    #
    @36
    @26
    wceq
    @16
    cA
    @3
    @15
    wfo
    #
    @40
    cA
    @3
    @15
    dff1o3
    simprbi
    cA
    cB
    @15
    imadif
    syl
    eleq2d
    sylibd
    @26
    @34
    n0i
    syl6
    syl5bir
    exlimdv
    imp
    sylan2
    @22
    @19
    ssdif0
    sylnibr
    @19
    @22
    dfpss3
    sylanbrc
    @16
    @23
    @21
    wb
    @1
    @16
    @22
    @3
    @19
    @16
    @15
    @15
    cdm
    #
    cima
    @15
    crn
    #
    @22
    @3
    @15
    imadmrn
    @16
    @42
    cA
    @15
    cA
    @3
    @15
    f1odm
    imaeq2d
    @16
    @41
    @43
    @3
    wceq
    cA
    @3
    @15
    f1ofo
    cA
    @3
    @15
    forn
    syl
    3eqtr3a
    psseq2d
    adantr
    mpbid
    @3
    @19
    php
    sylan2
    @18
    @13
    @20
    wi
    #
    @6
    @18
    cB
    @19
    cen
    wbr
    #
    @44
    @18
    cB
    @19
    @15
    cB
    cres
    #
    wf1o
    #
    @45
    @16
    cA
    @3
    @15
    wf1
    @11
    @47
    @1
    cA
    @3
    @15
    f1of1
    @12
    cA
    @3
    cB
    @15
    f1ores
    syl2an
    @47
    cB
    @19
    @28
    wf1o
    #
    vy
    wex
    @45
    @48
    @47
    vy
    @46
    @15
    cB
    vf
    vex
    resex
    cB
    @19
    @28
    @46
    f1oeq1
    spcev
    cB
    @19
    vy
    bren
    sylibr
    syl
    @13
    @45
    @20
    @3
    cB
    @19
    entr
    expcom
    syl
    adantl
    mtod
    exp32
    exlimdv
    syl5bi
    imp31
    @4
    @9
    @13
    wi
    @6
    @1
    @9
    @4
    cB
    @3
    cen
    wbr
    #
    @13
    @9
    @4
    @49
    cB
    cA
    @3
    entr
    ex
    cB
    @3
    ensym
    syl6com
    ad2antlr
    mtod
    cB
    cA
    brsdom
    sylanbrc
    exp31
    rexlimiv
    sylbi
    imp
end
