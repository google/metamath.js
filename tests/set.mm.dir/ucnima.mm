include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "cima.mm"
include "wss.mm"
include "wi.mm"
include "wa.mm"
include "wrex.mm"
include "wbr.mm"
include "wf.mm"
include "cucn.mm"
include "co.mm"
include "cust.mm"
include "wb.mm"
include "isucn.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "breq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "cxp.mm"
include "simplll.mm"
include "simplr.mm"
include "jca.mm"
include "ustssxp.mm"
include "sylan.mm"
include "sselda.mm"
include "adantlr.mm"
include "simpr.mm"
include "cop.mm"
include "elxp2.mm"
include "sylib.mm"
include "eleq1d.mm"
include "df-br.mm"
include "syl6bbr.mm"
include "c1st.mm"
include "c2nd.mm"
include "cvv.mm"
include "opex.mm"
include "ucnimalem.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "1st2nd2.mm"
include "syl.mm"
include "eqtr3d.mm"
include "vex.mm"
include "opth.mm"
include "simpld.mm"
include "fveq2d.mm"
include "opeq12d.mm"
include "eqtr4d.mm"
include "imbi12d.mm"
include "exbiri.mm"
include "reximdv.mm"
include "mpd.mm"
include "r19.29d2r.mm"
include "pm3.35.mm"
include "rexlimivw.mm"
include "imp.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "ex.mm"
include "reximdva.mm"
include "wfun.mm"
include "cdm.mm"
include "mpt2fun.mm"
include "dmmpt2.mm"
include "syl6sseqr.mm"
include "funimass4.mm"
include "sylancr.mm"
include "biimprd.mm"
include "r19.29r.mm"
include "reximi.mm"

theorem ucnima
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vp: setvar p
  let vw: setvar w
  assume ucnprima.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume ucnprima.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume ucnprima.3: |- ( ph -> F e. ( U uCn V ) )
  assume ucnprima.4: |- ( ph -> W e. V )
  assume ucnprima.5: |- G = ( x e. X , y e. X |-> <. ( F ` x ) , ( F ` y ) >. )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X x
  disjoint X y
  disjoint r x
  disjoint r y
  disjoint F r
  disjoint G x
  disjoint G y
  disjoint U r
  disjoint U x
  disjoint U y
  disjoint V r
  disjoint V x
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint X r
  disjoint Y r
  disjoint Y x
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint p x
  disjoint p y
  disjoint F p
  disjoint X p
  disjoint p r
  disjoint p w
  disjoint r w
  disjoint w x
  disjoint w y
  disjoint F w
  disjoint G p
  disjoint U p
  disjoint U w
  disjoint V w
  disjoint W p
  disjoint W w
  disjoint X w
  disjoint Y w
  disjoint p ph
  assert |- ( ph -> E. r e. U ( G " r ) C_ W )

  proof
    wph
    vp
    cv
    #
    cG
    cfv
    #
    cW
    wcel
    #
    vp
    vr
    cv
    #
    wral
    #
    @4
    cG
    @3
    cima
    cW
    wss
    #
    wi
    #
    wa
    #
    vr
    cU
    wrex
    #
    @5
    vr
    cU
    wrex
    wph
    @4
    vr
    cU
    wrex
    #
    @6
    vr
    cU
    wral
    @8
    wph
    vx
    cv
    #
    vy
    cv
    #
    @3
    wbr
    #
    @10
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    cW
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    vr
    cU
    wrex
    #
    @9
    wph
    cW
    cV
    wcel
    @12
    @13
    @14
    vw
    cv
    #
    wbr
    #
    wi
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    vr
    cU
    wrex
    #
    vw
    cV
    wral
    #
    @19
    ucnprima.4
    wph
    cX
    cY
    cF
    wf
    #
    @25
    wph
    cF
    cU
    cV
    cucn
    co
    wcel
    #
    @26
    @25
    wa
    #
    ucnprima.3
    wph
    cU
    cX
    cust
    cfv
    wcel
    #
    cV
    cY
    cust
    cfv
    wcel
    @27
    @28
    wb
    ucnprima.1
    ucnprima.2
    vx
    vy
    cU
    cF
    cV
    cX
    cY
    vw
    vr
    isucn
    syl2anc
    mpbid
    simprd
    @24
    @19
    vw
    cW
    cV
    @20
    cW
    wceq
    #
    @23
    @17
    vr
    vx
    cU
    cX
    @30
    @22
    @16
    vy
    cX
    @30
    @21
    @15
    @12
    @13
    @14
    @20
    cW
    breq
    imbi2d
    ralbidv
    rexralbidv
    rspcv
    sylc
    wph
    @18
    @4
    vr
    cU
    wph
    @3
    cU
    wcel
    #
    wa
    #
    @18
    @4
    @32
    @18
    wa
    #
    @2
    vp
    @3
    @33
    @0
    @3
    wcel
    #
    wa
    #
    wph
    @18
    wa
    #
    @0
    cX
    cX
    cxp
    #
    wcel
    #
    @34
    @2
    @35
    wph
    @18
    wph
    @31
    @18
    @34
    simplll
    @32
    @18
    @34
    simplr
    jca
    @32
    @34
    @38
    @18
    @32
    @3
    @37
    @0
    wph
    @29
    @31
    @3
    @37
    wss
    ucnprima.1
    cU
    @3
    cX
    ustssxp
    sylan
    #
    sselda
    adantlr
    @33
    @34
    simpr
    @36
    @38
    wa
    #
    @34
    @2
    @40
    @16
    @16
    @34
    @2
    wi
    #
    wi
    #
    wa
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    @41
    @40
    @16
    @42
    vx
    vy
    cX
    cX
    wph
    @18
    @38
    simplr
    wph
    @38
    @42
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    #
    @18
    wph
    @38
    wa
    #
    @0
    @10
    @11
    cop
    #
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wrex
    #
    @46
    @47
    @38
    @51
    wph
    @38
    simpr
    vx
    vy
    @0
    cX
    cX
    elxp2
    sylib
    @47
    @50
    @45
    vx
    cX
    @47
    @49
    @42
    vy
    cX
    @47
    @49
    @41
    @16
    @47
    @49
    wa
    #
    @34
    @12
    @2
    @15
    @52
    @34
    @48
    @3
    wcel
    #
    @12
    wph
    @49
    @34
    @53
    wb
    @38
    wph
    @49
    wa
    @0
    @48
    @3
    wph
    @49
    simpr
    eleq1d
    adantlr
    @10
    @11
    @3
    df-br
    syl6bbr
    @52
    @2
    @13
    @14
    cop
    #
    cW
    wcel
    @15
    @52
    @1
    @54
    cW
    @52
    @1
    @0
    c1st
    cfv
    #
    cF
    cfv
    #
    @0
    c2nd
    cfv
    #
    cF
    cfv
    #
    cop
    #
    @54
    @52
    @38
    @59
    cvv
    wcel
    @1
    @59
    wceq
    wph
    @38
    @49
    simplr
    #
    @56
    @58
    opex
    vp
    @37
    @59
    cvv
    cG
    wph
    vx
    vy
    cU
    cF
    cG
    cV
    cW
    cX
    cY
    vp
    ucnprima.1
    ucnprima.2
    ucnprima.3
    ucnprima.4
    ucnprima.5
    ucnimalem
    fvmpt2
    sylancl
    @52
    @13
    @56
    @14
    @58
    @52
    @10
    @55
    cF
    @52
    @10
    @55
    wceq
    #
    @11
    @57
    wceq
    #
    @52
    @48
    @55
    @57
    cop
    #
    wceq
    @61
    @62
    wa
    @52
    @0
    @48
    @63
    @47
    @49
    simpr
    @52
    @38
    @0
    @63
    wceq
    @60
    @0
    cX
    cX
    1st2nd2
    syl
    eqtr3d
    @10
    @11
    @55
    @57
    vx
    vex
    vy
    vex
    opth
    sylib
    #
    simpld
    fveq2d
    @52
    @11
    @57
    cF
    @52
    @61
    @62
    @64
    simprd
    fveq2d
    opeq12d
    eqtr4d
    eleq1d
    @13
    @14
    cW
    df-br
    syl6bbr
    imbi12d
    exbiri
    reximdv
    reximdv
    mpd
    adantlr
    r19.29d2r
    @44
    @41
    vx
    cX
    @43
    @41
    vy
    cX
    @16
    @41
    pm3.35
    rexlimivw
    rexlimivw
    syl
    imp
    syl21anc
    ralrimiva
    ex
    reximdva
    mpd
    wph
    @6
    vr
    cU
    @32
    @5
    @4
    @32
    cG
    wfun
    @3
    cG
    cdm
    #
    wss
    @5
    @4
    wb
    vx
    vy
    cX
    cX
    @54
    cG
    ucnprima.5
    mpt2fun
    @32
    @3
    @37
    @65
    @39
    vx
    vy
    cX
    cX
    @54
    cG
    ucnprima.5
    @13
    @14
    opex
    dmmpt2
    syl6sseqr
    vp
    @3
    cW
    cG
    funimass4
    sylancr
    biimprd
    ralrimiva
    @4
    @6
    vr
    cU
    r19.29r
    syl2anc
    @7
    @5
    vr
    cU
    @4
    @5
    pm3.35
    reximi
    syl
end
