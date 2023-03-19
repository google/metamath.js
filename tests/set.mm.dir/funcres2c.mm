include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "wo.mm"
include "wi.mm"
include "orc.mm"
include "a1i.mm"
include "olc.mm"
include "wb.mm"
include "wa.mm"
include "chomf.mm"
include "cfv.mm"
include "cbs.mm"
include "cin.mm"
include "cxp.mm"
include "cres.mm"
include "cresc.mm"
include "chom.mm"
include "cv.mm"
include "eqid.mm"
include "csubc.mm"
include "wcel.mm"
include "wss.mm"
include "inss2.mm"
include "fullsubc.mm"
include "adantr.mm"
include "wfn.mm"
include "homffn.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fnssres.mm"
include "crn.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "frn.mm"
include "simpr.mm"
include "funcf1.mm"
include "ressbasss.mm"
include "syl6ss.mm"
include "jaodan.mm"
include "ssind.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "simplrl.mm"
include "simplrr.mm"
include "funcf2.mm"
include "wceq.mm"
include "resshom.mm"
include "ad2antrr.mm"
include "oveqd.mm"
include "feq3d.mm"
include "mpbird.mm"
include "an32s.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "ovresd.mm"
include "sseldi.mm"
include "homfval.mm"
include "eqtrd.mm"
include "funcres2b.mm"
include "cvv.mm"
include "eqidd.mm"
include "ccomf.mm"
include "cress.mm"
include "ressinbas.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fullresc.mm"
include "simpld.mm"
include "simprd.mm"
include "ccat.mm"
include "cop.mm"
include "df-br.mm"
include "funcrcl.mm"
include "sylbi.mm"
include "jaoi.mm"
include "elex.mm"
include "adantl.mm"
include "ovex.mm"
include "eqeltri.mm"
include "funcpropd.mm"
include "breqd.mm"
include "bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem funcres2c
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cS: class S
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume funcres2c.a: |- A = ( Base ` C )
  assume funcres2c.e: |- E = ( D |`s S )
  assume funcres2c.d: |- ( ph -> D e. Cat )
  assume funcres2c.r: |- ( ph -> S e. V )
  assume funcres2c.1: |- ( ph -> F : A --> S )


  assert |- ( ph -> ( F ( C Func D ) G <-> F ( C Func E ) G ) )

  proof
    wph
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    cF
    cG
    cC
    cE
    cfunc
    co
    #
    wbr
    #
    wo
    #
    @1
    @3
    @1
    @4
    wi
    wph
    @1
    @3
    orc
    a1i
    @3
    @4
    wi
    wph
    @3
    @1
    olc
    a1i
    wph
    @4
    @1
    @3
    wb
    wph
    @4
    wa
    #
    @1
    cF
    cG
    cC
    cD
    cD
    chomf
    cfv
    #
    cS
    cD
    cbs
    cfv
    #
    cin
    #
    @8
    cxp
    #
    cres
    #
    cresc
    co
    #
    cfunc
    co
    #
    wbr
    @3
    @5
    vx
    vy
    cA
    cC
    cD
    @10
    @8
    cF
    cG
    cC
    chom
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    @13
    co
    #
    funcres2c.a
    @13
    eqid
    #
    wph
    @10
    cD
    csubc
    cfv
    wcel
    @4
    wph
    @7
    cD
    @8
    @6
    @7
    eqid
    #
    @6
    eqid
    #
    funcres2c.d
    @8
    @7
    wss
    #
    wph
    cS
    @7
    inss2
    #
    a1i
    #
    fullsubc
    adantr
    @10
    @9
    wfn
    #
    @5
    @6
    @7
    @7
    cxp
    #
    wfn
    @9
    @24
    wss
    #
    @23
    @7
    cD
    @6
    @19
    @18
    homffn
    @20
    @20
    @25
    @21
    @21
    @8
    @7
    @8
    @7
    xpss12
    mp2an
    @24
    @9
    @6
    fnssres
    mp2an
    a1i
    @5
    cF
    cA
    wfn
    #
    cF
    crn
    #
    @8
    wss
    cA
    @8
    cF
    wf
    #
    @5
    cA
    cS
    cF
    wf
    #
    @26
    wph
    @29
    @4
    funcres2c.1
    adantr
    #
    cA
    cS
    cF
    ffn
    syl
    @5
    @27
    cS
    @7
    @5
    @29
    @27
    cS
    wss
    @30
    cA
    cS
    cF
    frn
    syl
    wph
    @1
    @27
    @7
    wss
    #
    @3
    wph
    @1
    wa
    #
    cA
    @7
    cF
    wf
    @31
    @32
    cA
    @7
    cC
    cD
    cF
    cG
    funcres2c.a
    @18
    wph
    @1
    simpr
    funcf1
    cA
    @7
    cF
    frn
    syl
    wph
    @3
    wa
    #
    @27
    cE
    cbs
    cfv
    #
    @7
    @33
    cA
    @34
    cF
    wf
    @27
    @34
    wss
    @33
    cA
    @34
    cC
    cE
    cF
    cG
    funcres2c.a
    @34
    eqid
    wph
    @3
    simpr
    funcf1
    cA
    @34
    cF
    frn
    syl
    cS
    @7
    cE
    cD
    funcres2c.e
    @18
    ressbasss
    syl6ss
    jaodan
    ssind
    cA
    @8
    cF
    df-f
    sylanbrc
    #
    @5
    @14
    cA
    wcel
    #
    @15
    cA
    wcel
    #
    wa
    #
    wa
    #
    @16
    @14
    cF
    cfv
    #
    @15
    cF
    cfv
    #
    @10
    co
    #
    @14
    @15
    cG
    co
    #
    wf
    @16
    @40
    @41
    cD
    chom
    cfv
    #
    co
    #
    @43
    wf
    #
    wph
    @38
    @4
    @46
    wph
    @38
    wa
    #
    @1
    @46
    @3
    @47
    @1
    wa
    cA
    cC
    cD
    cF
    cG
    @13
    @44
    @14
    @15
    funcres2c.a
    @17
    @44
    eqid
    #
    @47
    @1
    simpr
    wph
    @36
    @37
    @1
    simplrl
    wph
    @36
    @37
    @1
    simplrr
    funcf2
    @47
    @3
    wa
    #
    @46
    @16
    @40
    @41
    cE
    chom
    cfv
    #
    co
    #
    @43
    wf
    @49
    cA
    cC
    cE
    cF
    cG
    @13
    @50
    @14
    @15
    funcres2c.a
    @17
    @50
    eqid
    @47
    @3
    simpr
    wph
    @36
    @37
    @3
    simplrl
    wph
    @36
    @37
    @3
    simplrr
    funcf2
    @49
    @45
    @51
    @43
    @16
    @49
    @44
    @50
    @40
    @41
    wph
    @44
    @50
    wceq
    #
    @38
    @3
    wph
    cS
    cV
    wcel
    #
    @52
    funcres2c.r
    cS
    cD
    cE
    @44
    cV
    funcres2c.e
    @48
    resshom
    syl
    ad2antrr
    oveqd
    feq3d
    mpbird
    jaodan
    an32s
    @39
    @42
    @45
    @43
    @16
    @39
    @42
    @40
    @41
    @6
    co
    @45
    @39
    @40
    @41
    @6
    @8
    @39
    cA
    @8
    @14
    cF
    @5
    @28
    @38
    @35
    adantr
    #
    @5
    @36
    @37
    simprl
    ffvelrnd
    #
    @39
    cA
    @8
    @15
    cF
    @54
    @5
    @36
    @37
    simprr
    ffvelrnd
    #
    ovresd
    @39
    @7
    cD
    @6
    @44
    @40
    @41
    @19
    @18
    @48
    @39
    @8
    @7
    @40
    @21
    @55
    sseldi
    @39
    @8
    @7
    @41
    @21
    @56
    sseldi
    homfval
    eqtrd
    feq3d
    mpbird
    funcres2b
    @5
    @2
    @12
    cF
    cG
    @5
    cC
    cC
    cE
    @11
    cvv
    @5
    cC
    chomf
    cfv
    eqidd
    @5
    cC
    ccomf
    cfv
    eqidd
    wph
    cE
    chomf
    cfv
    #
    @11
    chomf
    cfv
    #
    wceq
    @4
    wph
    @57
    cD
    @8
    cress
    co
    #
    chomf
    cfv
    #
    @58
    wph
    cE
    @59
    chomf
    wph
    cE
    cD
    cS
    cress
    co
    #
    @59
    funcres2c.e
    wph
    @53
    @61
    @59
    wceq
    funcres2c.r
    cS
    @7
    cD
    cV
    @18
    ressinbas
    syl
    syl5eq
    #
    fveq2d
    wph
    @60
    @58
    wceq
    #
    @59
    ccomf
    cfv
    #
    @11
    ccomf
    cfv
    #
    wceq
    #
    wph
    @7
    cD
    @59
    @8
    @11
    @6
    @18
    @19
    funcres2c.d
    @22
    @59
    eqid
    @11
    eqid
    fullresc
    #
    simpld
    eqtrd
    adantr
    wph
    cE
    ccomf
    cfv
    #
    @65
    wceq
    @4
    wph
    @68
    @64
    @65
    wph
    cE
    @59
    ccomf
    @62
    fveq2d
    wph
    @63
    @66
    @67
    simprd
    eqtrd
    adantr
    @4
    cC
    cvv
    wcel
    #
    wph
    @4
    cC
    ccat
    wcel
    #
    @69
    @1
    @70
    @3
    @1
    @70
    cD
    ccat
    wcel
    #
    @1
    cF
    cG
    cop
    #
    @0
    wcel
    @70
    @71
    wa
    cF
    cG
    @0
    df-br
    cC
    cD
    @72
    funcrcl
    sylbi
    simpld
    @3
    @70
    cE
    ccat
    wcel
    #
    @3
    @72
    @2
    wcel
    @70
    @73
    wa
    cF
    cG
    @2
    df-br
    cC
    cE
    @72
    funcrcl
    sylbi
    simpld
    jaoi
    cC
    ccat
    elex
    syl
    adantl
    #
    @74
    cE
    cvv
    wcel
    @5
    cE
    @61
    cvv
    funcres2c.e
    cD
    cS
    cress
    ovex
    eqeltri
    a1i
    @11
    cvv
    wcel
    @5
    cD
    @10
    cresc
    ovex
    a1i
    funcpropd
    breqd
    bitr4d
    ex
    pm5.21ndd
end
