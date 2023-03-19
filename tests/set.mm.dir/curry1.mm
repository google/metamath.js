include "cxp.mm"
include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "co.mm"
include "wceq.mm"
include "c2nd.mm"
include "csn.mm"
include "cvv.mm"
include "cres.mm"
include "ccnv.mm"
include "ccom.mm"
include "wfun.mm"
include "cdm.mm"
include "fnfun.mm"
include "wf1o.mm"
include "2ndconst.mm"
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
include "xpeq2i.mm"
include "wss.mm"
include "snssi.mm"
include "df-ss.mm"
include "sylib.mm"
include "xpeq1d.mm"
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
include "mpan2.mm"
include "ad2antlr.mm"
include "cop.mm"
include "snidg.mm"
include "jctir.mm"
include "opelxp.mm"
include "sylibr.mm"
include "jca.mm"
include "fvres.mm"
include "op2ndg.mm"
include "f1ocnvfv.mm"
include "sylc.mm"
include "fveq2d.mm"
include "adantll.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "mpteq2dva.mm"

theorem curry1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cD: class D
  assume curry1.1: |- G = ( F o. `' ( 2nd |` ( { C } X. _V ) ) )

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  disjoint G x
  disjoint D x
  assert |- ( ( F Fn ( A X. B ) /\ C e. A ) -> G = ( x e. B |-> ( C F x ) ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    #
    cC
    cA
    wcel
    #
    wa
    #
    cG
    vx
    cB
    vx
    cv
    #
    cG
    cfv
    #
    cmpt
    #
    vx
    cB
    cC
    @4
    cF
    co
    #
    cmpt
    @3
    cG
    cB
    wfn
    #
    cG
    @6
    wceq
    @3
    cF
    c2nd
    cC
    csn
    #
    cvv
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
    cB
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
    cC
    cvv
    cA
    2ndconst
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
    cB
    cF
    @12
    dmco
    @3
    @22
    @20
    @0
    cima
    #
    cB
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
    cB
    wceq
    @1
    @2
    @23
    c2nd
    @10
    @0
    cin
    #
    cres
    #
    crn
    #
    cB
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
    c2nd
    @10
    @0
    resres
    rneqi
    3eqtri
    @2
    @26
    c2nd
    @9
    cB
    cxp
    #
    cres
    #
    crn
    #
    cB
    @2
    @25
    @29
    @2
    @24
    @28
    c2nd
    @2
    @24
    @9
    cA
    cin
    #
    cB
    cxp
    #
    @28
    @24
    @31
    cvv
    cB
    cin
    #
    cxp
    @32
    @9
    cvv
    cA
    cB
    inxp
    @33
    cB
    @31
    @33
    cB
    cvv
    cin
    cB
    cvv
    cB
    incom
    cB
    inv1
    eqtri
    xpeq2i
    eqtri
    @2
    @31
    @9
    cB
    @2
    @9
    cA
    wss
    @31
    @9
    wceq
    cC
    cA
    snssi
    @9
    cA
    df-ss
    sylib
    xpeq1d
    syl5eq
    reseq2d
    rneqd
    @2
    @28
    cB
    @29
    wf1o
    @28
    cB
    @29
    wfo
    @30
    cB
    wceq
    cC
    cB
    cA
    2ndconst
    @28
    cB
    @29
    f1ofo
    @28
    cB
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
    cB
    wfn
    @14
    @16
    wa
    cB
    cG
    @13
    curry1.1
    fneq1i
    @13
    cB
    df-fn
    bitri
    sylanbrc
    vx
    cB
    cG
    dffn5
    sylib
    @3
    vx
    cB
    @5
    @7
    @3
    @4
    cB
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
    curry1.1
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
    @39
    @2
    @11
    @10
    wfn
    #
    @40
    @2
    @18
    @41
    @40
    wa
    @19
    @10
    cvv
    @11
    dff1o4
    sylib
    simprd
    @40
    @4
    cvv
    wcel
    #
    @39
    vx
    vex
    #
    cvv
    cF
    @12
    @4
    fvco2
    mpan2
    syl
    ad2antlr
    syl5eq
    @35
    @37
    cC
    @4
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
    #
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
    @2
    @47
    @34
    @2
    cC
    @9
    wcel
    #
    @42
    wa
    @47
    @2
    @50
    @42
    cC
    cA
    snidg
    @43
    jctir
    cC
    @4
    @9
    cvv
    opelxp
    sylibr
    #
    adantr
    jca
    @2
    @49
    @34
    @2
    @48
    @44
    c2nd
    cfv
    #
    @4
    @2
    @47
    @48
    @52
    wceq
    @51
    @44
    @10
    c2nd
    fvres
    syl
    @2
    @42
    @52
    @4
    wceq
    @43
    cC
    @4
    cA
    cvv
    op2ndg
    mpan2
    eqtrd
    adantr
    @10
    cvv
    @44
    @4
    @11
    f1ocnvfv
    sylc
    fveq2d
    adantll
    cC
    @4
    cF
    df-ov
    syl6eqr
    eqtrd
    mpteq2dva
    eqtrd
end
