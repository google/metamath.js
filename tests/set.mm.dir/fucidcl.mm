include "c1st.mm"
include "cfv.mm"
include "ccom.mm"
include "co.mm"
include "wcel.mm"
include "cbs.mm"
include "cv.mm"
include "chom.mm"
include "cixp.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "wceq.mm"
include "wral.mm"
include "cmpt.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "ccat.mm"
include "cfunc.mm"
include "wa.mm"
include "funcrcl.mm"
include "syl.mm"
include "simprd.mm"
include "eqid.mm"
include "cidfn.mm"
include "dffn2.mm"
include "sylib.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcf1.mm"
include "fcompt.mm"
include "syl2anc.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "catidcl.mm"
include "ralrimiva.mm"
include "wb.mm"
include "fvex.mm"
include "mptelixpg.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "eqeltrd.mm"
include "w3a.mm"
include "simpr1.mm"
include "syldan.mm"
include "simpr2.mm"
include "ffvelrnd.mm"
include "funcf2.mm"
include "simpr3.mm"
include "catlid.mm"
include "catrid.mm"
include "eqtr4d.mm"
include "fvco3.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ralrimivvva.mm"
include "isnat2.mm"
include "mpbir2and.mm"

theorem fucidcl
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let c.1: class .1.
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume fucidcl.q: |- Q = ( C FuncCat D )
  assume fucidcl.n: |- N = ( C Nat D )
  assume fucidcl.x: |- .1. = ( Id ` D )
  assume fucidcl.f: |- ( ph -> F e. ( C Func D ) )


  assert |- ( ph -> ( .1. o. ( 1st ` F ) ) e. ( F N F ) )

  proof
    wph
    c.1
    cF
    c1st
    cfv
    #
    ccom
    #
    cF
    cF
    cN
    co
    wcel
    @1
    vx
    cC
    cbs
    cfv
    #
    vx
    cv
    #
    @0
    cfv
    #
    @4
    cD
    chom
    cfv
    #
    co
    #
    cixp
    #
    wcel
    vy
    cv
    #
    @1
    cfv
    #
    vf
    cv
    #
    @3
    @8
    cF
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @4
    @8
    @0
    cfv
    #
    cop
    @14
    cD
    cco
    cfv
    #
    co
    #
    co
    #
    @13
    @3
    @1
    cfv
    #
    @4
    @4
    cop
    @14
    @15
    co
    #
    co
    #
    wceq
    #
    vf
    @3
    @8
    cC
    chom
    cfv
    #
    co
    #
    wral
    vy
    @2
    wral
    vx
    @2
    wral
    wph
    @1
    vx
    @2
    @4
    c.1
    cfv
    #
    cmpt
    #
    @7
    wph
    cD
    cbs
    cfv
    #
    cvv
    c.1
    wf
    #
    @2
    @26
    @0
    wf
    #
    @1
    @25
    wceq
    wph
    c.1
    @26
    wfn
    #
    @27
    wph
    cD
    ccat
    wcel
    #
    @29
    wph
    cC
    ccat
    wcel
    #
    @30
    wph
    cF
    cC
    cD
    cfunc
    co
    #
    wcel
    #
    @31
    @30
    wa
    fucidcl.f
    cC
    cD
    cF
    funcrcl
    syl
    simprd
    #
    @26
    cD
    c.1
    @26
    eqid
    #
    fucidcl.x
    cidfn
    syl
    @26
    c.1
    dffn2
    sylib
    wph
    @2
    @26
    cC
    cD
    @0
    @11
    @2
    eqid
    #
    @35
    wph
    @32
    wrel
    @33
    @0
    @11
    @32
    wbr
    #
    cC
    cD
    relfunc
    fucidcl.f
    cF
    @32
    1st2ndbr
    sylancr
    #
    funcf1
    #
    vx
    c.1
    @0
    @2
    @26
    cvv
    fcompt
    syl2anc
    wph
    @24
    @6
    wcel
    #
    vx
    @2
    wral
    #
    @25
    @7
    wcel
    #
    wph
    @40
    vx
    @2
    wph
    @3
    @2
    wcel
    #
    wa
    @26
    cD
    c.1
    @5
    @4
    @35
    @5
    eqid
    #
    fucidcl.x
    wph
    @30
    @43
    @34
    adantr
    wph
    @2
    @26
    @3
    @0
    @39
    ffvelrnda
    #
    catidcl
    ralrimiva
    @2
    cvv
    wcel
    @42
    @41
    wb
    cC
    cbs
    fvex
    vx
    @2
    @24
    @6
    cvv
    mptelixpg
    ax-mp
    sylibr
    eqeltrd
    wph
    @21
    vx
    vy
    vf
    @2
    @2
    @23
    wph
    @43
    @8
    @2
    wcel
    #
    @10
    @23
    wcel
    #
    w3a
    #
    wa
    #
    @14
    c.1
    cfv
    #
    @13
    @16
    co
    #
    @13
    @24
    @19
    co
    #
    @17
    @20
    @49
    @51
    @13
    @52
    @49
    @26
    cD
    @15
    c.1
    @13
    @5
    @4
    @14
    @35
    @44
    fucidcl.x
    wph
    @30
    @48
    @34
    adantr
    #
    wph
    @48
    @43
    @4
    @26
    wcel
    wph
    @43
    @46
    @47
    simpr1
    #
    @45
    syldan
    #
    @15
    eqid
    #
    @49
    @2
    @26
    @8
    @0
    wph
    @28
    @48
    @39
    adantr
    #
    wph
    @43
    @46
    @47
    simpr2
    #
    ffvelrnd
    #
    @49
    @23
    @4
    @14
    @5
    co
    @10
    @12
    @49
    @2
    cC
    cD
    @0
    @11
    @22
    @5
    @3
    @8
    @36
    @22
    eqid
    #
    @44
    wph
    @37
    @48
    @38
    adantr
    @54
    @58
    funcf2
    wph
    @43
    @46
    @47
    simpr3
    ffvelrnd
    #
    catlid
    @49
    @26
    cD
    @15
    c.1
    @13
    @5
    @4
    @14
    @35
    @44
    fucidcl.x
    @53
    @55
    @56
    @59
    @61
    catrid
    eqtr4d
    @49
    @9
    @50
    @13
    @16
    @49
    @28
    @46
    @9
    @50
    wceq
    @57
    @58
    @2
    @26
    @8
    c.1
    @0
    fvco3
    syl2anc
    oveq1d
    @49
    @18
    @24
    @13
    @19
    @49
    @28
    @43
    @18
    @24
    wceq
    @57
    @54
    @2
    @26
    @3
    c.1
    @0
    fvco3
    syl2anc
    oveq2d
    3eqtr4d
    ralrimivvva
    wph
    vx
    vy
    @1
    @2
    cC
    cD
    @15
    vf
    cF
    cF
    @22
    @5
    cN
    fucidcl.n
    @36
    @60
    @44
    @56
    fucidcl.f
    fucidcl.f
    isnat2
    mpbir2and
end
