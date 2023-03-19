include "cima.mm"
include "ctx.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "cfv.mm"
include "wceq.mm"
include "simp-6l.mm"
include "simpllr.mm"
include "syl2anc.mm"
include "simplr.mm"
include "wfn.mm"
include "cop.mm"
include "opex.mm"
include "fnmpt2i.mm"
include "a1i.mm"
include "ctopon.mm"
include "syl.mm"
include "toponss.mm"
include "xpss12.mm"
include "simprl.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "simp-4r.mm"
include "wf.mm"
include "ffn.mm"
include "3syl.mm"
include "fimaproj.mm"
include "3eltr3d.mm"
include "imass2.mm"
include "ad2antll.mm"
include "eqsstr3d.mm"
include "xpeq1.mm"
include "eleq2d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "wb.mm"
include "eltx.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "adantlr.mm"
include "adantr.mm"
include "r19.29vva.mm"
include "wfun.mm"
include "mpt2fun.mm"
include "fvelima.mm"
include "mpan.mm"
include "adantl.mm"
include "r19.29a.mm"
include "ralrimiva.mm"
include "mpbird.mm"

theorem txomap
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vz: setvar z
  assume txomap.f: |- ( ph -> F : X --> Z )
  assume txomap.g: |- ( ph -> G : Y --> T )
  assume txomap.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume txomap.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txomap.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume txomap.m: |- ( ph -> M e. ( TopOn ` T ) )
  assume txomap.1: |- ( ( ph /\ x e. J ) -> ( F " x ) e. L )
  assume txomap.2: |- ( ( ph /\ y e. K ) -> ( G " y ) e. M )
  assume txomap.a: |- ( ph -> A e. ( J tX K ) )
  assume txomap.h: |- H = ( x e. X , y e. Y |-> <. ( F ` x ) , ( G ` y ) >. )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint M x
  disjoint M y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A z
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint x z
  disjoint y z
  disjoint F a
  disjoint F b
  disjoint G b
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H z
  disjoint J z
  disjoint K z
  disjoint L a
  disjoint L b
  disjoint L c
  disjoint L z
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M z
  disjoint c ph
  disjoint ph z
  assert |- ( ph -> ( H " A ) e. ( L tX M ) )

  proof
    wph
    cH
    cA
    cima
    #
    cL
    cM
    ctx
    co
    wcel
    #
    vc
    cv
    #
    va
    cv
    #
    vb
    cv
    #
    cxp
    #
    wcel
    #
    @5
    @0
    wss
    #
    wa
    #
    vb
    cM
    wrex
    va
    cL
    wrex
    #
    vc
    @0
    wral
    #
    wph
    @9
    vc
    @0
    wph
    @2
    @0
    wcel
    #
    wa
    #
    vz
    cv
    #
    cH
    cfv
    #
    @2
    wceq
    #
    @9
    vz
    cA
    @12
    @13
    cA
    wcel
    #
    wa
    #
    @15
    wa
    #
    @13
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    wcel
    #
    @21
    cA
    wss
    #
    wa
    #
    @9
    vx
    vy
    cJ
    cK
    @18
    @19
    cJ
    wcel
    #
    wa
    #
    @20
    cK
    wcel
    #
    wa
    #
    @24
    wa
    #
    cF
    @19
    cima
    #
    cL
    wcel
    #
    cG
    @20
    cima
    #
    cM
    wcel
    #
    @2
    @30
    @32
    cxp
    #
    wcel
    #
    @34
    @0
    wss
    #
    @9
    @29
    wph
    @25
    @31
    wph
    @11
    @16
    @15
    @25
    @27
    @24
    simp-6l
    #
    @18
    @25
    @27
    @24
    simpllr
    #
    txomap.1
    syl2anc
    @29
    wph
    @27
    @33
    @37
    @26
    @27
    @24
    simplr
    #
    txomap.2
    syl2anc
    @29
    @14
    cH
    @21
    cima
    #
    @2
    @34
    @29
    cH
    cX
    cY
    cxp
    #
    wfn
    #
    @21
    @41
    wss
    #
    @22
    @14
    @40
    wcel
    @42
    @29
    vx
    vy
    cX
    cY
    @19
    cF
    cfv
    #
    @20
    cG
    cfv
    #
    cop
    #
    cH
    txomap.h
    @44
    @45
    opex
    fnmpt2i
    a1i
    @29
    @19
    cX
    wss
    #
    @20
    cY
    wss
    #
    @43
    @29
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    @25
    @47
    @29
    wph
    @50
    @37
    txomap.j
    syl
    @38
    @19
    cJ
    cX
    toponss
    syl2anc
    #
    @29
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @27
    @48
    @29
    wph
    @53
    @37
    txomap.k
    syl
    @39
    @20
    cK
    cY
    toponss
    syl2anc
    #
    @19
    cX
    @20
    cY
    xpss12
    syl2anc
    @28
    @22
    @23
    simprl
    @41
    @21
    cH
    @13
    fnfvima
    syl3anc
    @17
    @15
    @25
    @27
    @24
    simp-4r
    @29
    vx
    vy
    cX
    cY
    cF
    cG
    cH
    @19
    @20
    txomap.h
    @29
    wph
    cX
    cZ
    cF
    wf
    cF
    cX
    wfn
    @37
    txomap.f
    cX
    cZ
    cF
    ffn
    3syl
    @29
    wph
    cY
    cT
    cG
    wf
    cG
    cY
    wfn
    @37
    txomap.g
    cY
    cT
    cG
    ffn
    3syl
    @51
    @54
    fimaproj
    #
    3eltr3d
    @29
    @34
    @40
    @0
    @55
    @23
    @40
    @0
    wss
    @28
    @22
    @21
    cA
    cH
    imass2
    ad2antll
    eqsstr3d
    @8
    @35
    @36
    wa
    @2
    @30
    @4
    cxp
    #
    wcel
    #
    @56
    @0
    wss
    #
    wa
    va
    vb
    @30
    @32
    cL
    cM
    @3
    @30
    wceq
    #
    @6
    @57
    @7
    @58
    @59
    @5
    @56
    @2
    @3
    @30
    @4
    xpeq1
    #
    eleq2d
    @59
    @5
    @56
    @0
    @60
    sseq1d
    anbi12d
    @4
    @32
    wceq
    #
    @57
    @35
    @58
    @36
    @61
    @56
    @34
    @2
    @4
    @32
    @30
    xpeq2
    #
    eleq2d
    @61
    @56
    @34
    @0
    @62
    sseq1d
    anbi12d
    rspc2ev
    syl112anc
    @17
    @24
    vy
    cK
    wrex
    vx
    cJ
    wrex
    #
    @15
    wph
    @16
    @63
    @11
    wph
    @63
    vz
    cA
    wph
    cA
    cJ
    cK
    ctx
    co
    wcel
    #
    @63
    vz
    cA
    wral
    #
    txomap.a
    wph
    @50
    @53
    @64
    @65
    wb
    txomap.j
    txomap.k
    vx
    vy
    cA
    cJ
    cK
    @49
    @52
    vz
    eltx
    syl2anc
    mpbid
    r19.21bi
    adantlr
    adantr
    r19.29vva
    @11
    @15
    vz
    cA
    wrex
    #
    wph
    cH
    wfun
    @11
    @66
    vx
    vy
    cX
    cY
    @46
    cH
    txomap.h
    mpt2fun
    vz
    @2
    cA
    cH
    fvelima
    mpan
    adantl
    r19.29a
    ralrimiva
    wph
    cL
    cZ
    ctopon
    cfv
    #
    wcel
    cM
    cT
    ctopon
    cfv
    #
    wcel
    @1
    @10
    wb
    txomap.l
    txomap.m
    va
    vb
    @0
    cL
    cM
    @67
    @68
    vc
    eltx
    syl2anc
    mpbird
end
