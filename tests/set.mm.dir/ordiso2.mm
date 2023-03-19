include "cep.mm"
include "wiso.mm"
include "word.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wcel.mm"
include "con0.mm"
include "wss.mm"
include "ordsson.mm"
include "3ad2ant2.mm"
include "sseld.mm"
include "wi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "wa.mm"
include "wb.mm"
include "ordelss.mm"
include "3ad2antl2.mm"
include "sselda.mm"
include "pm5.5.mm"
include "syl.mm"
include "ralbidva.mm"
include "ccnv.mm"
include "wf1o.mm"
include "isof1o.mm"
include "3ad2ant1.mm"
include "ad2antrr.mm"
include "simpll3.mm"
include "simpr.mm"
include "wf.mm"
include "f1of.mm"
include "simplrl.mm"
include "ffvelrn.mm"
include "syl2anc.mm"
include "jca.mm"
include "ordtr1.mm"
include "sylc.mm"
include "f1ocnvfv2.mm"
include "eqeltrd.mm"
include "wbr.mm"
include "simpll1.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "isorel.mm"
include "syl12anc.mm"
include "vex.mm"
include "epelc.mm"
include "fvex.mm"
include "3bitr3g.mm"
include "mpbird.mm"
include "simplrr.mm"
include "rspcv.mm"
include "eqtr3d.mm"
include "simprr.mm"
include "rspccva.mm"
include "sylan.mm"
include "epel.mm"
include "biimpri.mm"
include "adantl.mm"
include "simpl2.mm"
include "simprl.mm"
include "mpbid.mm"
include "sylib.mm"
include "eqeltrrd.mm"
include "impbida.mm"
include "eqrdv.mm"
include "expr.mm"
include "sylbid.mm"
include "ex.mm"
include "com23.mm"
include "a2i.mm"
include "a1i.mm"
include "syl5bi.mm"
include "tfis2.mm"
include "com3l.mm"
include "mpdd.mm"
include "ralrimiv.mm"
include "adantll.mm"
include "3ad2antl1.mm"
include "adantlr.mm"
include "wrex.mm"
include "crn.mm"
include "simpl1.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "eleq2d.mm"
include "wfn.mm"
include "f1ofn.mm"
include "adantr.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "simpl.mm"
include "simplr.mm"
include "exp43.mm"
include "syldd.mm"
include "imp.mm"
include "rexlimdv.mm"
include "impbid.mm"
include "mpdan.mm"

theorem ordiso2
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F Isom _E , _E ( A , B ) /\ Ord A /\ Ord B ) -> A = B )

  proof
    cA
    cB
    cep
    cep
    cF
    wiso
    #
    cA
    word
    #
    cB
    word
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    vx
    cA
    wral
    #
    cA
    cB
    wceq
    @3
    @6
    vx
    cA
    @3
    @4
    cA
    wcel
    #
    @4
    con0
    wcel
    #
    @6
    @3
    cA
    con0
    @4
    @1
    @0
    cA
    con0
    wss
    @2
    cA
    ordsson
    3ad2ant2
    sseld
    @9
    @3
    @8
    @6
    @3
    @8
    @6
    wi
    #
    wi
    #
    @3
    vy
    cv
    #
    cA
    wcel
    #
    @12
    cF
    cfv
    #
    @12
    wceq
    #
    wi
    #
    wi
    #
    vx
    vy
    @4
    @12
    wceq
    #
    @10
    @16
    @3
    @18
    @8
    @13
    @6
    @15
    @4
    @12
    cA
    eleq1
    @18
    @5
    @14
    @4
    @12
    @4
    @12
    cF
    fveq2
    @18
    id
    eqeq12d
    imbi12d
    imbi2d
    @17
    vy
    @4
    wral
    @3
    @16
    vy
    @4
    wral
    #
    wi
    #
    @9
    @11
    @3
    @16
    vy
    @4
    r19.21v
    @20
    @11
    wi
    @9
    @3
    @19
    @10
    @3
    @8
    @19
    @6
    @3
    @8
    @19
    @6
    wi
    @3
    @8
    wa
    #
    @19
    @15
    vy
    @4
    wral
    #
    @6
    @21
    @16
    @15
    vy
    @4
    @21
    @12
    @4
    wcel
    wa
    @13
    @16
    @15
    wb
    @21
    @4
    cA
    @12
    @1
    @0
    @8
    @4
    cA
    wss
    #
    @2
    cA
    @4
    ordelss
    #
    3ad2antl2
    sselda
    @13
    @15
    pm5.5
    syl
    ralbidva
    @3
    @8
    @22
    @6
    @3
    @8
    @22
    wa
    #
    wa
    #
    vz
    @5
    @4
    @26
    vz
    cv
    #
    @5
    wcel
    #
    @27
    @4
    wcel
    #
    @26
    @28
    wa
    #
    @27
    @27
    cF
    ccnv
    #
    cfv
    #
    @4
    @30
    @32
    cF
    cfv
    #
    @27
    @32
    @30
    cA
    cB
    cF
    wf1o
    #
    @27
    cB
    wcel
    #
    @33
    @27
    wceq
    @3
    @34
    @25
    @28
    @0
    @1
    @34
    @2
    cA
    cB
    cep
    cep
    cF
    isof1o
    #
    3ad2ant1
    ad2antrr
    #
    @30
    @2
    @28
    @5
    cB
    wcel
    #
    wa
    @35
    @0
    @1
    @2
    @25
    @28
    simpll3
    @30
    @28
    @38
    @26
    @28
    simpr
    #
    @30
    cA
    cB
    cF
    wf
    #
    @8
    @38
    @3
    @40
    @25
    @28
    @0
    @1
    @40
    @2
    @0
    @34
    @40
    @36
    cA
    cB
    cF
    f1of
    syl
    #
    3ad2ant1
    ad2antrr
    @3
    @8
    @22
    @28
    simplrl
    #
    cA
    cB
    @4
    cF
    ffvelrn
    syl2anc
    jca
    @27
    @5
    cB
    ordtr1
    sylc
    #
    cA
    cB
    @27
    cF
    f1ocnvfv2
    syl2anc
    #
    @30
    @32
    @4
    wcel
    #
    @22
    @33
    @32
    wceq
    #
    @30
    @45
    @33
    @5
    wcel
    #
    @30
    @33
    @27
    @5
    @44
    @39
    eqeltrd
    @30
    @32
    @4
    cep
    wbr
    #
    @33
    @5
    cep
    wbr
    #
    @45
    @47
    @30
    @0
    @32
    cA
    wcel
    #
    @8
    @48
    @49
    wb
    @0
    @1
    @2
    @25
    @28
    simpll1
    @30
    cB
    cA
    @31
    wf
    #
    @35
    @50
    @30
    @34
    cB
    cA
    @31
    wf1o
    @51
    @37
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @31
    f1of
    3syl
    @43
    cB
    cA
    @27
    @31
    ffvelrn
    syl2anc
    @42
    cA
    cB
    @32
    @4
    cep
    cep
    cF
    isorel
    syl12anc
    @32
    @4
    vx
    vex
    epelc
    @33
    @5
    @4
    cF
    fvex
    #
    epelc
    3bitr3g
    mpbird
    #
    @3
    @8
    @22
    @28
    simplrr
    @15
    @46
    vy
    @32
    @4
    @12
    @32
    wceq
    #
    @14
    @33
    @12
    @32
    @12
    @32
    cF
    fveq2
    @54
    id
    eqeq12d
    rspcv
    sylc
    eqtr3d
    @53
    eqeltrd
    @26
    @29
    wa
    #
    @27
    cF
    cfv
    #
    @27
    @5
    @26
    @22
    @29
    @56
    @27
    wceq
    #
    @3
    @8
    @22
    simprr
    @15
    @57
    vy
    @27
    @4
    @12
    @27
    wceq
    #
    @14
    @56
    @12
    @27
    @12
    @27
    cF
    fveq2
    @58
    id
    eqeq12d
    rspccva
    sylan
    @55
    @56
    @5
    cep
    wbr
    #
    @56
    @5
    wcel
    @55
    @27
    @4
    cep
    wbr
    #
    @59
    @29
    @60
    @26
    @60
    @29
    vz
    vx
    epel
    biimpri
    adantl
    @55
    @0
    @27
    cA
    wcel
    #
    @8
    @60
    @59
    wb
    @0
    @1
    @2
    @25
    @29
    simpll1
    @26
    @4
    cA
    @27
    @26
    @1
    @8
    @23
    @0
    @1
    @2
    @25
    simpl2
    @3
    @8
    @22
    simprl
    @24
    syl2anc
    sselda
    @3
    @8
    @22
    @29
    simplrl
    cA
    cB
    @27
    @4
    cep
    cep
    cF
    isorel
    syl12anc
    mpbid
    @56
    @5
    @52
    epelc
    sylib
    eqeltrrd
    impbida
    eqrdv
    expr
    sylbid
    ex
    com23
    a2i
    a1i
    syl5bi
    tfis2
    com3l
    mpdd
    ralrimiv
    @3
    @7
    wa
    #
    vz
    cA
    cB
    @62
    @61
    @35
    @62
    @61
    @35
    @62
    @61
    wa
    @56
    @27
    cB
    @7
    @61
    @57
    @3
    @6
    @57
    vx
    @27
    cA
    @4
    @27
    wceq
    #
    @5
    @56
    @4
    @27
    @4
    @27
    cF
    fveq2
    @63
    id
    eqeq12d
    rspccva
    adantll
    @3
    @61
    @56
    cB
    wcel
    #
    @7
    @0
    @1
    @61
    @64
    @2
    @0
    @40
    @61
    @64
    @41
    cA
    cB
    @27
    cF
    ffvelrn
    sylan
    3ad2antl1
    adantlr
    eqeltrrd
    ex
    @62
    @35
    vw
    cv
    #
    cF
    cfv
    #
    @27
    wceq
    #
    vw
    cA
    wrex
    #
    @61
    @62
    @27
    cF
    crn
    #
    wcel
    #
    @35
    @68
    @62
    @69
    cB
    @27
    @62
    @0
    @69
    cB
    wceq
    #
    @0
    @1
    @2
    @7
    simpl1
    @0
    @34
    cA
    cB
    cF
    wfo
    @71
    @36
    cA
    cB
    cF
    f1ofo
    cA
    cB
    cF
    forn
    3syl
    syl
    eleq2d
    @62
    cF
    cA
    wfn
    #
    @70
    @68
    wb
    @3
    @72
    @7
    @0
    @1
    @72
    @2
    @0
    @34
    @72
    @36
    cA
    cB
    cF
    f1ofn
    syl
    3ad2ant1
    adantr
    vw
    cA
    @27
    cF
    fvelrnb
    syl
    bitr3d
    @62
    @67
    @61
    vw
    cA
    @3
    @7
    @65
    cA
    wcel
    #
    @67
    @61
    wi
    #
    wi
    @3
    @73
    @7
    @74
    @3
    @73
    @7
    @66
    @65
    wceq
    #
    @74
    @73
    @7
    @75
    wi
    wi
    @3
    @6
    @75
    vx
    @65
    cA
    @4
    @65
    wceq
    #
    @5
    @66
    @4
    @65
    @4
    @65
    cF
    fveq2
    @76
    id
    eqeq12d
    rspcv
    a1i
    @3
    @73
    @75
    @67
    @61
    @3
    @73
    wa
    #
    @75
    @67
    wa
    #
    wa
    @27
    @65
    cA
    @78
    @27
    @65
    wceq
    @77
    @78
    @66
    @27
    @65
    @75
    @67
    simpr
    @75
    @67
    simpl
    eqtr3d
    adantl
    @3
    @73
    @78
    simplr
    eqeltrd
    exp43
    syldd
    com23
    imp
    rexlimdv
    sylbid
    impbid
    eqrdv
    mpdan
end
