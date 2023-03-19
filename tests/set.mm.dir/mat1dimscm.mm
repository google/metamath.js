include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cxp.mm"
include "cop.mm"
include "cmulr.mm"
include "cfv.mm"
include "cof.mm"
include "co.mm"
include "cmpt.mm"
include "cvsca.mm"
include "cvv.mm"
include "wfn.mm"
include "opex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "anim2i.mm"
include "ancomd.mm"
include "fnsng.mm"
include "syl.mm"
include "adantl.mm"
include "wceq.mm"
include "xpsng.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "sneqi.mm"
include "syl6eqr.mm"
include "anidms.mm"
include "ad2antlr.mm"
include "xpeq1d.mm"
include "sylan.mm"
include "snex.mm"
include "inidm.mm"
include "cv.mm"
include "wi.mm"
include "elsni.mm"
include "fveq2.mm"
include "eqcomi.mm"
include "opeq1i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "fveq1d.mm"
include "fvsng.mm"
include "sylan9eq.mm"
include "ex.mm"
include "impcom.mm"
include "offval.mm"
include "cbs.mm"
include "simprl.mm"
include "w3a.mm"
include "simpr.mm"
include "df-3an.mm"
include "sylibr.mm"
include "mat1dimbas.mm"
include "eqid.mm"
include "matvsca2.mm"
include "syl2anc.mm"
include "3anass.mm"
include "biimpri.mm"
include "adantlr.mm"
include "ringcl.mm"
include "fmptsn.mm"
include "sylancr.mm"
include "3eqtr4d.mm"

theorem mat1dimscm
  let cA: class A
  let cB: class B
  let cR: class R
  let cE: class E
  let cO: class O
  let cV: class V
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume mat1dim.a: |- A = ( { E } Mat R )
  assume mat1dim.b: |- B = ( Base ` R )
  assume mat1dim.o: |- O = <. E , E >.


  assert |- ( ( ( R e. Ring /\ E e. V ) /\ ( X e. B /\ Y e. B ) ) -> ( X ( .s ` A ) { <. O , Y >. } ) = { <. O , ( X ( .r ` R ) Y ) >. } )

  proof
    cR
    crg
    wcel
    #
    cE
    cV
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    wa
    #
    cE
    csn
    #
    @7
    cxp
    #
    cX
    csn
    #
    cxp
    #
    cO
    cY
    cop
    csn
    #
    cR
    cmulr
    cfv
    #
    cof
    co
    #
    vx
    cO
    csn
    #
    cX
    cY
    @12
    co
    #
    cmpt
    #
    cX
    @11
    cA
    cvsca
    cfv
    #
    co
    #
    cO
    @15
    cop
    csn
    #
    @6
    vx
    @14
    @14
    cX
    cY
    @12
    @14
    @10
    @11
    cvv
    cvv
    @6
    @10
    @14
    wfn
    @14
    @9
    cxp
    #
    @14
    wfn
    #
    @6
    @21
    cO
    cX
    cop
    #
    csn
    #
    @14
    wfn
    #
    @5
    @24
    @2
    @5
    cO
    cvv
    wcel
    #
    @3
    wa
    #
    @24
    @5
    @3
    @25
    @4
    @25
    @3
    @25
    @4
    cO
    cE
    cE
    cop
    #
    cvv
    mat1dim.o
    cE
    cE
    opex
    #
    eqeltri
    #
    a1i
    anim2i
    ancomd
    #
    cO
    cX
    cvv
    cB
    fnsng
    syl
    adantl
    @6
    @14
    @20
    @23
    @5
    @20
    @23
    wceq
    #
    @2
    @5
    @26
    @31
    @30
    cO
    cX
    cvv
    cB
    xpsng
    syl
    adantl
    fneq1d
    mpbird
    @6
    @14
    @10
    @20
    @6
    @8
    @14
    @9
    @1
    @8
    @14
    wceq
    #
    @0
    @5
    @1
    @32
    @1
    @1
    wa
    @8
    @27
    csn
    #
    @14
    cE
    cE
    cV
    cV
    xpsng
    #
    cO
    @27
    mat1dim.o
    sneqi
    syl6eqr
    anidms
    ad2antlr
    xpeq1d
    fneq1d
    mpbird
    @5
    @11
    @14
    wfn
    #
    @2
    @3
    @25
    @4
    @35
    @25
    @3
    @29
    a1i
    #
    cO
    cY
    cvv
    cB
    fnsng
    sylan
    adantl
    @14
    cvv
    wcel
    @6
    cO
    snex
    a1i
    #
    @37
    @14
    inidm
    vx
    cv
    #
    @14
    wcel
    #
    @6
    @38
    @10
    cfv
    #
    cX
    wceq
    #
    @39
    @38
    cO
    wceq
    #
    @6
    @41
    wi
    @38
    cO
    elsni
    #
    @42
    @6
    @41
    @42
    @6
    @40
    cO
    @10
    cfv
    #
    cX
    @38
    cO
    @10
    fveq2
    @6
    @44
    cO
    @23
    cfv
    #
    cX
    @6
    cO
    @10
    @23
    @6
    @10
    @33
    @9
    cxp
    #
    @23
    @6
    @8
    @33
    @9
    @1
    @8
    @33
    wceq
    #
    @0
    @5
    @1
    @47
    @34
    anidms
    ad2antlr
    xpeq1d
    @5
    @46
    @23
    wceq
    #
    @2
    @5
    @27
    cvv
    wcel
    #
    @3
    wa
    #
    @48
    @5
    @3
    @49
    @4
    @49
    @3
    @49
    @4
    @28
    a1i
    anim2i
    ancomd
    @50
    @46
    @27
    cX
    cop
    #
    csn
    @23
    @27
    cX
    cvv
    cB
    xpsng
    @51
    @22
    @27
    cO
    cX
    cO
    @27
    mat1dim.o
    eqcomi
    opeq1i
    sneqi
    syl6eq
    syl
    adantl
    eqtrd
    fveq1d
    @5
    @45
    cX
    wceq
    #
    @2
    @5
    @26
    @52
    @30
    cO
    cX
    cvv
    cB
    fvsng
    syl
    adantl
    eqtrd
    sylan9eq
    ex
    syl
    impcom
    @39
    @6
    @38
    @11
    cfv
    #
    cY
    wceq
    #
    @39
    @42
    @6
    @54
    wi
    @43
    @42
    @6
    @54
    @42
    @6
    @53
    cO
    @11
    cfv
    #
    cY
    @38
    cO
    @11
    fveq2
    @5
    @55
    cY
    wceq
    #
    @2
    @3
    @25
    @4
    @56
    @36
    cO
    cY
    cvv
    cB
    fvsng
    sylan
    adantl
    sylan9eq
    ex
    syl
    impcom
    offval
    @6
    @3
    @11
    cA
    cbs
    cfv
    #
    wcel
    #
    @18
    @13
    wceq
    @2
    @3
    @4
    simprl
    @6
    @0
    @1
    @4
    w3a
    #
    @58
    @6
    @2
    @4
    wa
    @59
    @5
    @4
    @2
    @3
    @4
    simpr
    anim2i
    @0
    @1
    @4
    df-3an
    sylibr
    cA
    cB
    cR
    cE
    cO
    cV
    cY
    mat1dim.a
    mat1dim.b
    mat1dim.o
    mat1dimbas
    syl
    cA
    @57
    @8
    cR
    @17
    @12
    cB
    @7
    cX
    @11
    mat1dim.a
    @57
    eqid
    mat1dim.b
    @17
    eqid
    @12
    eqid
    #
    @8
    eqid
    matvsca2
    syl2anc
    @6
    @25
    @15
    cB
    wcel
    #
    @19
    @16
    wceq
    @29
    @6
    @0
    @3
    @4
    w3a
    #
    @61
    @0
    @5
    @62
    @1
    @62
    @0
    @5
    wa
    @0
    @3
    @4
    3anass
    biimpri
    adantlr
    cB
    cR
    @12
    cX
    cY
    mat1dim.b
    @60
    ringcl
    syl
    vx
    cO
    @15
    cvv
    cB
    fmptsn
    sylancr
    3eqtr4d
end
