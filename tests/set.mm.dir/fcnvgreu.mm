include "wrel.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wceq.mm"
include "wreu.mm"
include "c1st.mm"
include "cdm.mm"
include "df-rn.mm"
include "eleq2i.mm"
include "fgreu.mm"
include "adantll.mm"
include "sylan2b.mm"
include "wb.mm"
include "cop.mm"
include "cnvcnvss.mm"
include "csn.mm"
include "cuni.mm"
include "cxp.mm"
include "cnvssrndm.mm"
include "sseli.mm"
include "dfdm4.mm"
include "xpeq12i.mm"
include "syl6eleq.mm"
include "2nd1st.mm"
include "syl.mm"
include "eqcomd.mm"
include "relcnv.mm"
include "cnvf1olem.mm"
include "simpld.mm"
include "mpan.mm"
include "mpdan.mm"
include "sseldi.mm"
include "adantl.mm"
include "wral.mm"
include "wrex.mm"
include "simpll.mm"
include "simpr.mm"
include "wss.mm"
include "relssdmrn.mm"
include "adantr.mm"
include "sselda.mm"
include "syl12anc.mm"
include "a1i.mm"
include "simplr.mm"
include "ad2antlr.mm"
include "simprd.mm"
include "sneqd.mm"
include "cnveqd.mm"
include "unieqd.mm"
include "ad2antrr.mm"
include "3eqtr2d.mm"
include "impbida.mm"
include "ralrimiva.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "reu6.mm"
include "sylibr.mm"
include "fvex.mm"
include "op2ndd.mm"
include "eqeq2d.mm"
include "reuxfr4d.mm"
include "mpbird.mm"

theorem fcnvgreu
  let cA: class A
  let cY: class Y
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r

  disjoint A p
  disjoint Y p
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint A q
  disjoint A r
  disjoint Y q
  assert |- ( ( ( Rel A /\ Fun `' A ) /\ Y e. ran A ) -> E! p e. A Y = ( 2nd ` p ) )

  proof
    cA
    wrel
    #
    cA
    ccnv
    #
    wfun
    #
    wa
    #
    cY
    cA
    crn
    #
    wcel
    #
    wa
    cY
    vp
    cv
    #
    c2nd
    cfv
    #
    wceq
    #
    vp
    cA
    wreu
    #
    cY
    vq
    cv
    #
    c1st
    cfv
    #
    wceq
    #
    vq
    @1
    wreu
    #
    @5
    @3
    cY
    @1
    cdm
    #
    wcel
    #
    @13
    @4
    @14
    cY
    cA
    df-rn
    #
    eleq2i
    @2
    @15
    @13
    @0
    @1
    cY
    vq
    fgreu
    adantll
    sylan2b
    @3
    @9
    @13
    wb
    @5
    @3
    @8
    @12
    vp
    vq
    @10
    c2nd
    cfv
    #
    @11
    cop
    #
    cA
    @1
    @10
    @1
    wcel
    #
    @18
    cA
    wcel
    @3
    @19
    @1
    ccnv
    #
    cA
    @18
    cA
    cnvcnvss
    @19
    @18
    @10
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    #
    @18
    @20
    wcel
    #
    @19
    @23
    @18
    @19
    @10
    @14
    @1
    crn
    #
    cxp
    #
    wcel
    @23
    @18
    wceq
    #
    @19
    @10
    @4
    cA
    cdm
    #
    cxp
    #
    @27
    @1
    @30
    @10
    cA
    cnvssrndm
    sseli
    @4
    @14
    @29
    @26
    @16
    cA
    dfdm4
    xpeq12i
    syl6eleq
    @10
    @14
    @26
    2nd1st
    syl
    #
    eqcomd
    #
    @1
    wrel
    #
    @19
    @24
    wa
    #
    @25
    cA
    relcnv
    #
    @33
    @34
    wa
    #
    @25
    @10
    @18
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    #
    @1
    @10
    @18
    cnvf1olem
    #
    simpld
    mpan
    mpdan
    sseldi
    adantl
    @3
    @6
    cA
    wcel
    #
    wa
    #
    @6
    @18
    wceq
    #
    @10
    vr
    cv
    #
    wceq
    #
    wb
    #
    vq
    @1
    wral
    #
    vr
    @1
    wrex
    #
    @44
    vq
    @1
    wreu
    @43
    @7
    @6
    c1st
    cfv
    cop
    #
    @1
    wcel
    #
    @44
    @10
    @50
    wceq
    #
    wb
    #
    vq
    @1
    wral
    #
    @49
    @43
    @0
    @42
    @50
    @6
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    #
    @51
    @0
    @2
    @42
    simpll
    #
    @3
    @42
    simpr
    #
    @43
    @57
    @50
    @43
    @6
    @29
    @4
    cxp
    #
    wcel
    @57
    @50
    wceq
    #
    @3
    cA
    @61
    @6
    @0
    cA
    @61
    wss
    @2
    cA
    relssdmrn
    adantr
    sselda
    @6
    @29
    @4
    2nd1st
    syl
    #
    eqcomd
    #
    @0
    @42
    @58
    wa
    wa
    #
    @51
    @6
    @50
    csn
    #
    ccnv
    #
    cuni
    #
    wceq
    #
    cA
    @6
    @50
    cnvf1olem
    #
    simpld
    syl12anc
    @43
    @53
    vq
    @1
    @43
    @19
    wa
    #
    @44
    @52
    @71
    @44
    wa
    #
    @10
    @39
    @57
    @50
    @72
    @33
    @19
    @24
    @40
    @33
    @72
    @35
    a1i
    @43
    @19
    @44
    simplr
    @19
    @24
    @43
    @44
    @32
    ad2antlr
    @36
    @25
    @40
    @41
    simprd
    syl12anc
    @72
    @56
    @38
    @72
    @55
    @37
    @72
    @6
    @18
    @71
    @44
    simpr
    sneqd
    cnveqd
    unieqd
    @43
    @62
    @19
    @44
    @63
    ad2antrr
    3eqtr2d
    @71
    @52
    wa
    #
    @6
    @68
    @23
    @18
    @43
    @69
    @19
    @52
    @43
    @0
    @42
    @58
    @69
    @59
    @60
    @64
    @65
    @51
    @69
    @70
    simprd
    syl12anc
    ad2antrr
    @73
    @22
    @67
    @73
    @21
    @66
    @73
    @10
    @50
    @71
    @52
    simpr
    sneqd
    cnveqd
    unieqd
    @19
    @28
    @43
    @52
    @31
    ad2antlr
    3eqtr2d
    impbida
    ralrimiva
    @48
    @54
    vr
    @50
    @1
    @45
    @50
    wceq
    #
    @47
    @53
    vq
    @1
    @74
    @46
    @52
    @44
    @45
    @50
    @10
    eqeq2
    bibi2d
    ralbidv
    rspcev
    syl2anc
    @44
    vq
    vr
    @1
    reu6
    sylibr
    @44
    @8
    @12
    wb
    @3
    @44
    @7
    @11
    cY
    @17
    @11
    @6
    @10
    c2nd
    fvex
    @10
    c1st
    fvex
    op2ndd
    eqeq2d
    adantl
    reuxfr4d
    adantr
    mpbird
end
