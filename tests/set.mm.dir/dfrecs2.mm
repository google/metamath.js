include "crecs.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "cfuns.mm"
include "cdomain.mm"
include "ccnv.mm"
include "cima.mm"
include "cin.mm"
include "cep.mm"
include "ccom.mm"
include "capply.mm"
include "cfullfn.mm"
include "crestrict.mm"
include "cfix.mm"
include "cdif.mm"
include "cdm.mm"
include "dfrecs3.mm"
include "wcel.mm"
include "wn.mm"
include "wex.mm"
include "wfun.mm"
include "elin.mm"
include "vex.mm"
include "elfuns.mm"
include "wbr.mm"
include "brcnv.mm"
include "brdomain.mm"
include "bitri.mm"
include "rexbii.mm"
include "elima.mm"
include "risset.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "eldm.mm"
include "brdif.mm"
include "brco.mm"
include "anbi1i.mm"
include "exbii.mm"
include "dmex.mm"
include "breq1.mm"
include "ceqsexv.mm"
include "epelc.mm"
include "3bitri.mm"
include "cop.mm"
include "df-br.mm"
include "opex.mm"
include "elfix.mm"
include "ancom.mm"
include "brapply.mm"
include "fvex.mm"
include "breq2.mm"
include "brrestrict.mm"
include "resex.mm"
include "brfullfun.mm"
include "notbii.mm"
include "df-rex.mm"
include "rexnal.mm"
include "3bitr2ri.mm"
include "con1bii.mm"
include "anass.mm"
include "eleq1.mm"
include "raleq.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "df-fn.mm"
include "eqcom.mm"
include "anbi2i.mm"
include "an12.mm"
include "3bitr3ri.mm"
include "3bitr2i.mm"
include "eldif.mm"
include "abbi2i.mm"
include "unieqi.mm"
include "eqtr4i.mm"

theorem dfrecs2
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- recs ( F ) = U. ( ( Funs i^i ( `' Domain " On ) ) \ dom ( ( `' _E o. Domain ) \ Fix ( `' Apply o. ( FullFun F o. Restrict ) ) ) )

  proof
    cF
    crecs
    vf
    cv
    #
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    @0
    cfv
    #
    @0
    @3
    cres
    #
    cF
    cfv
    wceq
    #
    vy
    @1
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    vf
    cab
    #
    cuni
    cfuns
    cdomain
    ccnv
    #
    con0
    cima
    #
    cin
    #
    cep
    ccnv
    #
    cdomain
    ccom
    #
    capply
    ccnv
    #
    cF
    cfullfn
    #
    crestrict
    ccom
    #
    ccom
    #
    cfix
    #
    cdif
    #
    cdm
    #
    cdif
    #
    cuni
    vx
    vy
    vf
    cF
    dfrecs3
    @23
    @10
    @9
    vf
    @23
    @0
    @13
    wcel
    #
    @0
    @22
    wcel
    #
    wn
    #
    wa
    #
    @1
    con0
    wcel
    #
    @8
    wa
    #
    vx
    wex
    #
    @0
    @23
    wcel
    @9
    @27
    @0
    wfun
    #
    @0
    cdm
    #
    con0
    wcel
    #
    @6
    vy
    @32
    wral
    #
    wa
    #
    wa
    #
    @1
    @32
    wceq
    #
    @31
    @28
    @7
    wa
    #
    wa
    #
    wa
    #
    vx
    wex
    @30
    @27
    @31
    @33
    wa
    #
    @34
    wa
    @36
    @24
    @41
    @26
    @34
    @24
    @0
    cfuns
    wcel
    #
    @0
    @12
    wcel
    #
    wa
    @41
    @0
    cfuns
    @12
    elin
    @42
    @31
    @43
    @33
    @0
    vf
    vex
    #
    elfuns
    @1
    @0
    @11
    wbr
    #
    vx
    con0
    wrex
    @37
    vx
    con0
    wrex
    @43
    @33
    @45
    @37
    vx
    con0
    @45
    @0
    @1
    cdomain
    wbr
    #
    @37
    @1
    @0
    cdomain
    vx
    vex
    #
    @44
    brcnv
    @0
    @1
    @44
    @47
    brdomain
    #
    bitri
    rexbii
    vx
    @0
    @11
    con0
    @44
    elima
    vx
    @32
    con0
    risset
    3bitr4i
    anbi12i
    bitri
    @34
    @25
    @25
    @3
    @32
    wcel
    #
    @6
    wn
    #
    wa
    #
    vy
    wex
    #
    @50
    vy
    @32
    wrex
    @34
    wn
    @25
    @0
    @3
    @21
    wbr
    #
    vy
    wex
    @52
    vy
    @0
    @21
    @44
    eldm
    @53
    @51
    vy
    @53
    @0
    @3
    @15
    wbr
    #
    @0
    @3
    @20
    wbr
    #
    wn
    #
    wa
    @51
    @0
    @3
    @15
    @20
    brdif
    @54
    @49
    @56
    @50
    @54
    @46
    @1
    @3
    @14
    wbr
    #
    wa
    #
    vx
    wex
    #
    @32
    @3
    @14
    wbr
    #
    @49
    vx
    @0
    @3
    @14
    cdomain
    @44
    vy
    vex
    #
    brco
    @59
    @37
    @57
    wa
    #
    vx
    wex
    @60
    @58
    @62
    vx
    @46
    @37
    @57
    @48
    anbi1i
    exbii
    @57
    @60
    vx
    @32
    @0
    @44
    dmex
    #
    @1
    @32
    @3
    @14
    breq1
    ceqsexv
    bitri
    @60
    @3
    @32
    cep
    wbr
    @49
    @32
    @3
    cep
    @63
    @61
    brcnv
    @3
    @32
    @63
    epelc
    bitri
    3bitri
    @55
    @6
    @55
    @0
    @3
    cop
    #
    @20
    wcel
    @64
    @64
    @19
    wbr
    #
    @6
    @0
    @3
    @20
    df-br
    @64
    @19
    @0
    @3
    opex
    #
    elfix
    @65
    @64
    @1
    @18
    wbr
    #
    @1
    @64
    @16
    wbr
    #
    wa
    #
    vx
    wex
    #
    @64
    @4
    @18
    wbr
    #
    @6
    vx
    @64
    @64
    @16
    @18
    @66
    @66
    brco
    @70
    @1
    @4
    wceq
    #
    @67
    wa
    #
    vx
    wex
    @71
    @69
    @73
    vx
    @69
    @68
    @67
    wa
    @73
    @67
    @68
    ancom
    @68
    @72
    @67
    @68
    @64
    @1
    capply
    wbr
    @72
    @1
    @64
    capply
    @47
    @66
    brcnv
    @0
    @3
    @1
    @44
    @61
    @47
    brapply
    bitri
    anbi1i
    bitri
    exbii
    @67
    @71
    vx
    @4
    @3
    @0
    fvex
    #
    @1
    @4
    @64
    @18
    breq2
    ceqsexv
    bitri
    @71
    @64
    @1
    crestrict
    wbr
    #
    @1
    @4
    @17
    wbr
    #
    wa
    #
    vx
    wex
    #
    @5
    @4
    @17
    wbr
    #
    @6
    vx
    @64
    @4
    @17
    crestrict
    @66
    @74
    brco
    @78
    @1
    @5
    wceq
    #
    @76
    wa
    #
    vx
    wex
    @79
    @77
    @81
    vx
    @75
    @80
    @76
    @0
    @3
    @1
    @44
    @61
    @47
    brrestrict
    anbi1i
    exbii
    @76
    @79
    vx
    @5
    @0
    @3
    @44
    resex
    #
    @1
    @5
    @4
    @17
    breq1
    ceqsexv
    bitri
    @5
    @4
    cF
    @82
    @74
    brfullfun
    3bitri
    3bitri
    3bitri
    notbii
    anbi12i
    bitri
    exbii
    bitri
    @50
    vy
    @32
    df-rex
    @6
    vy
    @32
    rexnal
    3bitr2ri
    con1bii
    anbi12i
    @31
    @33
    @34
    anass
    bitri
    @39
    @36
    vx
    @32
    @63
    @37
    @38
    @35
    @31
    @37
    @28
    @33
    @7
    @34
    @1
    @32
    con0
    eleq1
    @6
    vy
    @1
    @32
    raleq
    anbi12d
    anbi2d
    ceqsexv
    @40
    @29
    vx
    @2
    @38
    wa
    @37
    @31
    wa
    #
    @38
    wa
    @29
    @40
    @2
    @83
    @38
    @2
    @31
    @32
    @1
    wceq
    #
    wa
    @31
    @37
    wa
    @83
    @0
    @1
    df-fn
    @84
    @37
    @31
    @32
    @1
    eqcom
    anbi2i
    @31
    @37
    ancom
    3bitri
    anbi1i
    @2
    @28
    @7
    an12
    @37
    @31
    @38
    anass
    3bitr3ri
    exbii
    3bitr2i
    @0
    @13
    @22
    eldif
    @8
    vx
    con0
    df-rex
    3bitr4i
    abbi2i
    unieqi
    eqtr4i
end
