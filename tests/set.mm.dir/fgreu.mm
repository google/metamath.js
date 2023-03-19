include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "cop.mm"
include "funfvop.mm"
include "c2nd.mm"
include "wrel.mm"
include "simplll.mm"
include "funrel.mm"
include "syl.mm"
include "simplr.mm"
include "1st2nd.mm"
include "syl2anc.mm"
include "simpr.mm"
include "simpllr.mm"
include "opeq1d.mm"
include "eqtr4d.mm"
include "eqeltrrd.mm"
include "funopfvb.mm"
include "biimpar.mm"
include "syl21anc.mm"
include "opeq12d.mm"
include "fveq2d.mm"
include "cvv.mm"
include "fvex.mm"
include "op1stg.mm"
include "mpan2.mm"
include "ad3antlr.mm"
include "eqtr2d.mm"
include "impbida.mm"
include "ralrimiva.mm"
include "eqeq2.mm"
include "bibi2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "reu6.mm"
include "sylibr.mm"

theorem fgreu
  let cF: class F
  let cX: class X
  let vp: setvar p
  let vq: setvar q

  disjoint F p
  disjoint X p
  disjoint p q
  disjoint F q
  disjoint X q
  assert |- ( ( Fun F /\ X e. dom F ) -> E! p e. F X = ( 1st ` p ) )

  proof
    cF
    wfun
    #
    cX
    cF
    cdm
    #
    wcel
    #
    wa
    #
    cX
    vp
    cv
    #
    c1st
    cfv
    #
    wceq
    #
    @4
    vq
    cv
    #
    wceq
    #
    wb
    #
    vp
    cF
    wral
    #
    vq
    cF
    wrex
    #
    @6
    vp
    cF
    wreu
    @3
    cX
    cX
    cF
    cfv
    #
    cop
    #
    cF
    wcel
    @6
    @4
    @13
    wceq
    #
    wb
    #
    vp
    cF
    wral
    #
    @11
    cX
    cF
    funfvop
    @3
    @15
    vp
    cF
    @3
    @4
    cF
    wcel
    #
    wa
    #
    @6
    @14
    @18
    @6
    wa
    #
    @4
    @5
    @4
    c2nd
    cfv
    #
    cop
    #
    @13
    @19
    cF
    wrel
    #
    @17
    @4
    @21
    wceq
    @19
    @0
    @22
    @0
    @2
    @17
    @6
    simplll
    #
    cF
    funrel
    syl
    @3
    @17
    @6
    simplr
    #
    @4
    cF
    1st2nd
    syl2anc
    #
    @19
    cX
    @5
    @12
    @20
    @18
    @6
    simpr
    #
    @19
    @0
    @2
    cX
    @20
    cop
    #
    cF
    wcel
    #
    @12
    @20
    wceq
    #
    @23
    @0
    @2
    @17
    @6
    simpllr
    @19
    @4
    @27
    cF
    @19
    @4
    @21
    @27
    @25
    @19
    cX
    @5
    @20
    @26
    opeq1d
    eqtr4d
    @24
    eqeltrrd
    @3
    @29
    @28
    cX
    @20
    cF
    funopfvb
    biimpar
    syl21anc
    opeq12d
    eqtr4d
    @18
    @14
    wa
    #
    @5
    @13
    c1st
    cfv
    #
    cX
    @30
    @4
    @13
    c1st
    @18
    @14
    simpr
    fveq2d
    @2
    @31
    cX
    wceq
    #
    @0
    @17
    @14
    @2
    @12
    cvv
    wcel
    @32
    cX
    cF
    fvex
    cX
    @12
    @1
    cvv
    op1stg
    mpan2
    ad3antlr
    eqtr2d
    impbida
    ralrimiva
    @10
    @16
    vq
    @13
    cF
    @7
    @13
    wceq
    #
    @9
    @15
    vp
    cF
    @33
    @8
    @14
    @6
    @7
    @13
    @4
    eqeq2
    bibi2d
    ralbidv
    rspcev
    syl2anc
    @6
    vp
    vq
    cF
    reu6
    sylibr
end
