include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "co.mm"
include "wceq.mm"
include "c1st.mm"
include "cvv.mm"
include "csn.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wfun.mm"
include "cdm.mm"
include "fnfun.mm"
include "wf1o.mm"
include "1stconst.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "syl.mm"
include "funco.mm"
include "syl2an.mm"
include "cima.mm"
include "dmco.mm"
include "fndm.mm"
include "adantr.mm"
include "imaeq2d.mm"
include "cin.mm"
include "crn.mm"
include "imacnvcnv.mm"
include "df-ima.mm"
include "resres.mm"
include "rneqi.mm"
include "3eqtri.mm"
include "inxp.mm"
include "incom.mm"
include "inv1.mm"
include "eqtri.mm"
include "xpeq1i.mm"
include "wss.mm"
include "snssi.mm"
include "df-ss.mm"
include "sylib.mm"
include "xpeq2d.mm"
include "syl5eq.mm"
include "reseq2d.mm"
include "rneqd.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "eqtrd.mm"
include "adantl.mm"
include "fneq1i.mm"
include "df-fn.mm"
include "bitri.mm"
include "sylanbrc.mm"
include "dffn5.mm"
include "fveq1i.mm"
include "dff1o4.mm"
include "simprd.mm"
include "vex.mm"
include "fvco2.mm"
include "sylancl.mm"
include "ad2antlr.mm"
include "cop.mm"
include "a1i.mm"
include "snidg.mm"
include "opelxp.mm"
include "jca.mm"
include "fvres.mm"
include "op1stg.mm"
include "ancoms.mm"
include "f1ocnvfv.mm"
include "sylc.mm"
include "fveq2d.mm"
include "adantll.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"

theorem curry2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cD: class D
  assume curry2.1: |- G = ( F o. `' ( 1st |` ( _V X. { C } ) ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint G x
  disjoint D x
  assert |- ( ( F Fn ( A X. B ) /\ C e. B ) -> G = ( x e. A |-> ( x F C ) ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cB
    wcel
    #
    wa
    #
    cG
    vx
    cA
    vx
    cv
    #
    cG
    cfv
    #
    cmpt
    #
    vx
    cA
    @4
    cC
    cF
    co
    #
    cmpt
    @3
    cG
    cA
    wfn
    #
    cG
    @6
    wceq
    @3
    cF
    c1st
    cvv
    cC
    csn
    #
    cxp
    #
    cres
    #
    ccnv
    #
    ccom
    #
    wfun
    #
    @13
    cdm
    #
    cA
    wceq
    #
    @8
    @1
    cF
    wfun
    @12
    wfun
    #
    @14
    @2
    @0
    cF
    fnfun
    @2
    @10
    cvv
    @11
    wf1o
    #
    @17
    cvv
    cC
    cB
    1stconst
    #
    @18
    @10
    cvv
    @11
    wfo
    @17
    @10
    cvv
    @11
    dff1o3
    simprbi
    syl
    cF
    @12
    funco
    syl2an
    @3
    @15
    @12
    ccnv
    #
    cF
    cdm
    #
    cima
    #
    cA
    cF
    @12
    dmco
    @3
    @22
    @20
    @0
    cima
    #
    cA
    @3
    @21
    @0
    @20
    @1
    @21
    @0
    wceq
    @2
    @0
    cF
    fndm
    adantr
    imaeq2d
    @2
    @23
    cA
    wceq
    @1
    @2
    @23
    c1st
    @10
    @0
    cin
    #
    cres
    #
    crn
    #
    cA
    @23
    @11
    @0
    cima
    @11
    @0
    cres
    #
    crn
    @26
    @11
    @0
    imacnvcnv
    @11
    @0
    df-ima
    @27
    @25
    c1st
    @10
    @0
    resres
    rneqi
    3eqtri
    @2
    @26
    c1st
    cA
    @9
    cxp
    #
    cres
    #
    crn
    #
    cA
    @2
    @25
    @29
    @2
    @24
    @28
    c1st
    @2
    @24
    cA
    @9
    cB
    cin
    #
    cxp
    #
    @28
    @24
    cvv
    cA
    cin
    #
    @31
    cxp
    @32
    cvv
    @9
    cA
    cB
    inxp
    @33
    cA
    @31
    @33
    cA
    cvv
    cin
    cA
    cvv
    cA
    incom
    cA
    inv1
    eqtri
    xpeq1i
    eqtri
    @2
    @31
    @9
    cA
    @2
    @9
    cB
    wss
    @31
    @9
    wceq
    cC
    cB
    snssi
    @9
    cB
    df-ss
    sylib
    xpeq2d
    syl5eq
    reseq2d
    rneqd
    @2
    @28
    cA
    @29
    wf1o
    @28
    cA
    @29
    wfo
    @30
    cA
    wceq
    cA
    cC
    cB
    1stconst
    @28
    cA
    @29
    f1ofo
    @28
    cA
    @29
    forn
    3syl
    eqtrd
    syl5eq
    adantl
    eqtrd
    syl5eq
    @8
    @13
    cA
    wfn
    @14
    @16
    wa
    cA
    cG
    @13
    curry2.1
    fneq1i
    @13
    cA
    df-fn
    bitri
    sylanbrc
    vx
    cA
    cG
    dffn5
    sylib
    @3
    vx
    cA
    @5
    @7
    @3
    @4
    cA
    wcel
    #
    wa
    #
    @5
    @4
    @12
    cfv
    #
    cF
    cfv
    #
    @7
    @35
    @5
    @4
    @13
    cfv
    #
    @37
    @4
    cG
    @13
    curry2.1
    fveq1i
    @2
    @38
    @37
    wceq
    #
    @1
    @34
    @2
    @12
    cvv
    wfn
    #
    @4
    cvv
    wcel
    #
    @39
    @2
    @11
    @10
    wfn
    #
    @40
    @2
    @18
    @42
    @40
    wa
    @19
    @10
    cvv
    @11
    dff1o4
    sylib
    simprd
    vx
    vex
    #
    cvv
    cF
    @12
    @4
    fvco2
    sylancl
    ad2antlr
    syl5eq
    @35
    @37
    @4
    cC
    cop
    #
    cF
    cfv
    #
    @7
    @2
    @34
    @37
    @45
    wceq
    @1
    @2
    @34
    wa
    #
    @36
    @44
    cF
    @46
    @18
    @44
    @10
    wcel
    #
    wa
    @44
    @11
    cfv
    #
    @4
    wceq
    @36
    @44
    wceq
    @46
    @18
    @47
    @2
    @18
    @34
    @19
    adantr
    @46
    @41
    cC
    @9
    wcel
    #
    @47
    @41
    @46
    @43
    a1i
    @2
    @49
    @34
    cC
    cB
    snidg
    #
    adantr
    @4
    cC
    cvv
    @9
    opelxp
    #
    sylanbrc
    jca
    @46
    @48
    @44
    c1st
    cfv
    #
    @4
    @2
    @48
    @52
    wceq
    #
    @34
    @2
    @47
    @53
    @2
    @41
    @49
    @47
    @41
    @2
    @43
    a1i
    @50
    @51
    sylanbrc
    @44
    @10
    c1st
    fvres
    syl
    adantr
    @34
    @2
    @52
    @4
    wceq
    @4
    cC
    cA
    cB
    op1stg
    ancoms
    eqtrd
    @10
    cvv
    @44
    @4
    @11
    f1ocnvfv
    sylc
    fveq2d
    adantll
    @4
    cC
    cF
    df-ov
    syl6eqr
    eqtrd
    mpteq2dva
    eqtrd
end
