include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wn.mm"
include "wrex.mm"
include "wpss.mm"
include "wral.mm"
include "crn.mm"
include "cint.mm"
include "adantr.mm"
include "wss.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "peano2.mm"
include "fnfvelrn.mm"
include "syl2an.mm"
include "intss1.mm"
include "wb.mm"
include "fvelrnb.mm"
include "ad2antrr.mm"
include "simplrr.mm"
include "ad3antlr.mm"
include "simpr.mm"
include "simplrl.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "2a1i.mm"
include "cvv.mm"
include "elex.mm"
include "sucexb.mm"
include "sylibr.mm"
include "adantl.mm"
include "sucssel.mm"
include "imp.mm"
include "eleq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "mpd.mm"
include "eqtr3.mm"
include "expcom.mm"
include "syl6.mm"
include "a2d.mm"
include "findsg.mm"
include "impr.mm"
include "syl22anc.mm"
include "eqimss.mm"
include "simplll.mm"
include "isf32lem1.mm"
include "word.mm"
include "wo.mm"
include "nnord.mm"
include "ad2antlr.mm"
include "ad2antll.mm"
include "ordtri2or2.mm"
include "syl2anc.mm"
include "mpjaodan.mm"
include "anassrs.mm"
include "sseq2.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "ssint.mm"
include "eqssd.mm"
include "eqeltrd.mm"
include "mtand.mm"
include "rexnal.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "pm4.61.mm"
include "dfpss2.mm"
include "simplbi2.mm"
include "anim2d.mm"
include "syl5bi.mm"
include "ralimi.mm"
include "rexim.mm"
include "3syl.mm"

theorem isf32lem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let cB: class B
  let vt: setvar t
  let cL: class L
  let vc: setvar c
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vd: setvar d
  let cS: class S
  let cJ: class J
  let cK: class K
  assume isf32lem.a: |- ( ph -> F : _om --> ~P G )
  assume isf32lem.b: |- ( ph -> A. x e. _om ( F ` suc x ) C_ ( F ` x ) )
  assume isf32lem.c: |- ( ph -> -. |^| ran F e. ran F )

  disjoint a x
  disjoint G a
  disjoint a ph
  disjoint ph x
  disjoint A a
  disjoint A x
  disjoint F a
  disjoint F x
  disjoint a b
  disjoint a w
  disjoint B a
  disjoint b w
  disjoint b x
  disjoint B b
  disjoint w x
  disjoint B w
  disjoint B x
  disjoint a t
  disjoint b t
  disjoint G b
  disjoint G t
  disjoint L a
  disjoint L b
  disjoint L x
  disjoint a c
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint b c
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b ph
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c ph
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint ph s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint ph t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph y
  disjoint a d
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint A w
  disjoint A y
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F w
  disjoint F y
  disjoint S a
  disjoint S b
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint K a
  disjoint K b
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  assert |- ( ( ph /\ A e. _om ) -> E. a e. _om ( A e. a /\ ( F ` suc a ) C. ( F ` a ) ) )

  proof
    wph
    cA
    com
    wcel
    #
    wa
    #
    cA
    va
    cv
    #
    wcel
    #
    @2
    csuc
    #
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    wceq
    #
    wi
    #
    wn
    #
    va
    com
    wrex
    #
    @3
    @5
    @6
    wpss
    #
    wa
    #
    va
    com
    wrex
    #
    @1
    @8
    va
    com
    wral
    #
    wn
    @10
    @1
    @14
    cF
    crn
    #
    cint
    #
    @15
    wcel
    #
    wph
    @17
    wn
    @0
    isf32lem.c
    adantr
    @1
    @14
    wa
    #
    @16
    cA
    csuc
    #
    cF
    cfv
    #
    @15
    @18
    @16
    @20
    @18
    @20
    @15
    wcel
    #
    @16
    @20
    wss
    @1
    @21
    @14
    wph
    cF
    com
    wfn
    #
    @19
    com
    wcel
    #
    @21
    @0
    wph
    com
    cG
    cpw
    #
    cF
    wf
    @22
    isf32lem.a
    com
    @24
    cF
    ffn
    syl
    #
    cA
    peano2
    #
    com
    @19
    cF
    fnfvelrn
    syl2an
    adantr
    #
    @20
    @15
    intss1
    syl
    @18
    @20
    vb
    cv
    #
    wss
    #
    vb
    @15
    wral
    @20
    @16
    wss
    @18
    @29
    vb
    @15
    @18
    @28
    @15
    wcel
    #
    vc
    cv
    #
    cF
    cfv
    #
    @28
    wceq
    #
    vc
    com
    wrex
    #
    @29
    wph
    @30
    @34
    wb
    #
    @0
    @14
    wph
    @22
    @35
    @25
    vc
    com
    @28
    cF
    fvelrnb
    syl
    ad2antrr
    @18
    @33
    @29
    vc
    com
    @18
    @31
    com
    wcel
    #
    wa
    @20
    @32
    wss
    #
    @33
    @29
    @1
    @14
    @36
    @37
    @1
    @14
    @36
    wa
    #
    wa
    #
    @19
    @31
    wss
    #
    @37
    @31
    @19
    wss
    #
    @39
    @40
    wa
    #
    @20
    @32
    wceq
    #
    @37
    @42
    @36
    @23
    @40
    @14
    @43
    @1
    @14
    @36
    @40
    simplrr
    @0
    @23
    wph
    @38
    @40
    @26
    ad3antlr
    @39
    @40
    simpr
    @1
    @14
    @36
    @40
    simplrl
    @36
    @23
    wa
    @40
    @14
    @43
    @14
    @20
    @28
    cF
    cfv
    #
    wceq
    #
    wi
    @14
    @20
    @20
    wceq
    #
    wi
    @14
    @20
    vd
    cv
    #
    cF
    cfv
    #
    wceq
    #
    wi
    @14
    @20
    @47
    csuc
    #
    cF
    cfv
    #
    wceq
    #
    wi
    @14
    @43
    wi
    vb
    vd
    @31
    @19
    @28
    @19
    wceq
    #
    @45
    @46
    @14
    @53
    @44
    @20
    @20
    @28
    @19
    cF
    fveq2
    eqeq2d
    imbi2d
    @28
    @47
    wceq
    #
    @45
    @49
    @14
    @54
    @44
    @48
    @20
    @28
    @47
    cF
    fveq2
    eqeq2d
    imbi2d
    @28
    @50
    wceq
    #
    @45
    @52
    @14
    @55
    @44
    @51
    @20
    @28
    @50
    cF
    fveq2
    eqeq2d
    imbi2d
    @28
    @31
    wceq
    #
    @45
    @43
    @14
    @56
    @44
    @32
    @20
    @28
    @31
    cF
    fveq2
    eqeq2d
    imbi2d
    @46
    @23
    @14
    @20
    eqid
    2a1i
    @47
    com
    wcel
    #
    @23
    wa
    #
    @19
    @47
    wss
    #
    wa
    #
    @14
    @49
    @52
    @60
    @14
    @51
    @48
    wceq
    #
    @49
    @52
    wi
    @60
    cA
    @47
    wcel
    #
    @14
    @61
    wi
    #
    @58
    @59
    @62
    @58
    cA
    cvv
    wcel
    #
    @59
    @62
    wi
    @23
    @64
    @57
    @23
    @19
    cvv
    wcel
    @64
    @19
    com
    elex
    cA
    sucexb
    sylibr
    adantl
    cA
    @47
    cvv
    sucssel
    syl
    imp
    @57
    @62
    @63
    wi
    @23
    @59
    @57
    @14
    @62
    @61
    @8
    @62
    @61
    wi
    va
    @47
    com
    @2
    @47
    wceq
    #
    @3
    @62
    @7
    @61
    @2
    @47
    cA
    eleq2
    @65
    @5
    @51
    @6
    @48
    @65
    @4
    @50
    cF
    @2
    @47
    suceq
    fveq2d
    @2
    @47
    cF
    fveq2
    eqeq12d
    imbi12d
    rspcv
    com23
    ad2antrr
    mpd
    @49
    @61
    @52
    @20
    @51
    @48
    eqtr3
    expcom
    syl6
    a2d
    findsg
    impr
    syl22anc
    @20
    @32
    eqimss
    syl
    @39
    @41
    wa
    @23
    @36
    @41
    wph
    @37
    @0
    @23
    wph
    @38
    @41
    @26
    ad3antlr
    @1
    @14
    @36
    @41
    simplrr
    @39
    @41
    simpr
    wph
    @0
    @38
    @41
    simplll
    wph
    vx
    @19
    @31
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem1
    syl22anc
    @39
    @19
    word
    #
    @31
    word
    #
    @40
    @41
    wo
    @0
    @66
    wph
    @38
    @0
    @23
    @66
    @26
    @19
    nnord
    syl
    ad2antlr
    @36
    @67
    @1
    @14
    @31
    nnord
    ad2antll
    @19
    @31
    ordtri2or2
    syl2anc
    mpjaodan
    anassrs
    @32
    @28
    @20
    sseq2
    syl5ibcom
    rexlimdva
    sylbid
    ralrimiv
    vb
    @20
    @15
    ssint
    sylibr
    eqssd
    @27
    eqeltrd
    mtand
    @8
    va
    com
    rexnal
    sylibr
    @1
    @5
    @6
    wss
    #
    va
    com
    wral
    #
    @9
    @12
    wi
    #
    va
    com
    wral
    @10
    @13
    wi
    wph
    @69
    @0
    wph
    vx
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @71
    cF
    cfv
    #
    wss
    #
    vx
    com
    wral
    @69
    isf32lem.b
    @75
    @68
    vx
    va
    com
    @71
    @2
    wceq
    #
    @73
    @5
    @74
    @6
    @76
    @72
    @4
    cF
    @71
    @2
    suceq
    fveq2d
    @71
    @2
    cF
    fveq2
    sseq12d
    cbvralv
    sylib
    adantr
    @68
    @70
    va
    com
    @9
    @3
    @7
    wn
    #
    wa
    @68
    @12
    @3
    @7
    pm4.61
    @68
    @77
    @11
    @3
    @11
    @68
    @77
    @5
    @6
    dfpss2
    simplbi2
    anim2d
    syl5bi
    ralimi
    @9
    @12
    va
    com
    rexim
    3syl
    mpd
end
