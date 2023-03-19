include "cv.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cxko.mm"
include "cfv.mm"
include "cmpt2.mm"
include "ccnv.mm"
include "simprr.mm"
include "ctopon.mm"
include "adantr.mm"
include "cxp.mm"
include "wfn.mm"
include "cuni.mm"
include "wf.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "simpr.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "ffn.mm"
include "syl.mm"
include "fnov.mm"
include "eqeltrrd.mm"
include "cnmpt2k.mm"
include "adantrr.mm"
include "eqeltrd.mm"
include "wral.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfmpt.mm"
include "simplrr.mm"
include "fveq1d.mm"
include "cvv.mm"
include "simprl.mm"
include "toponmax.mm"
include "ad2antrr.mm"
include "mptexg.mm"
include "fvmpt2.mm"
include "eqtrd.mm"
include "ovex.mm"
include "sylancl.mm"
include "expr.mm"
include "ralrimi.mm"
include "jctil.mm"
include "ex.mm"
include "mpt2eq123.mm"
include "sylancr.mm"
include "eqtr4d.mm"
include "jca.mm"
include "ccmp.mm"
include "cnlly.mm"
include "nllytop.mm"
include "xkotopon.mm"
include "feqmptd.mm"
include "ffvelrnda.mm"
include "mpteq2dva.mm"
include "cnmptk2.mm"
include "nfmpt21.mm"
include "nfmpt22.mm"
include "oveqd.mm"
include "fvex.mm"
include "ovmpt4g.mm"
include "mp3an3.mm"
include "sylan9eq.mm"
include "mpteq12.mm"
include "mpteq2da.mm"
include "impbida.mm"
include "opabbidv.mm"
include "df-mpt.mm"
include "eqtri.mm"
include "cnveqi.mm"
include "cnvopab.mm"
include "3eqtr4g.mm"

theorem xkocnv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  assume xkohmeo.x: |- ( ph -> J e. ( TopOn ` X ) )
  assume xkohmeo.y: |- ( ph -> K e. ( TopOn ` Y ) )
  assume xkohmeo.f: |- F = ( f e. ( ( J tX K ) Cn L ) |-> ( x e. X |-> ( y e. Y |-> ( x f y ) ) ) )
  assume xkohmeo.j: |- ( ph -> J e. N-Locally Comp )
  assume xkohmeo.k: |- ( ph -> K e. N-Locally Comp )
  assume xkohmeo.l: |- ( ph -> L e. Top )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K y
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint L f
  disjoint L g
  disjoint L x
  disjoint L y
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint f t
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint g t
  disjoint g u
  disjoint g w
  disjoint g z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint J t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint J w
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint K t
  disjoint K u
  disjoint K w
  disjoint K z
  disjoint ph t
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint L t
  disjoint L u
  disjoint L w
  disjoint L z
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint Y t
  disjoint Y u
  disjoint Y w
  disjoint Y z
  assert |- ( ph -> `' F = ( g e. ( J Cn ( L ^ko K ) ) |-> ( x e. X , y e. Y |-> ( ( g ` x ) ` y ) ) ) )

  proof
    wph
    vf
    cv
    #
    cJ
    cK
    ctx
    co
    #
    cL
    ccn
    co
    #
    wcel
    #
    vg
    cv
    #
    vx
    cX
    vy
    cY
    vx
    cv
    #
    vy
    cv
    #
    @0
    co
    #
    cmpt
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vg
    vf
    copab
    #
    @4
    cJ
    cL
    cK
    cxko
    co
    #
    ccn
    co
    #
    wcel
    #
    @0
    vx
    vy
    cX
    cY
    @6
    @5
    @4
    cfv
    #
    cfv
    #
    cmpt2
    #
    wceq
    #
    wa
    #
    vg
    vf
    copab
    cF
    ccnv
    #
    vg
    @14
    @18
    cmpt
    wph
    @11
    @20
    vg
    vf
    wph
    @11
    @20
    wph
    @11
    wa
    #
    @15
    @19
    @22
    @4
    @9
    @14
    wph
    @3
    @10
    simprr
    wph
    @3
    @9
    @14
    wcel
    @10
    wph
    @3
    wa
    #
    vx
    vy
    @7
    cJ
    cK
    cL
    cX
    cY
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @3
    xkohmeo.x
    adantr
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @3
    xkohmeo.y
    adantr
    @23
    @0
    vx
    vy
    cX
    cY
    @7
    cmpt2
    #
    @2
    @23
    @0
    cX
    cY
    cxp
    #
    wfn
    #
    @0
    @26
    wceq
    #
    @23
    @27
    cL
    cuni
    #
    @0
    wf
    #
    @28
    @23
    @1
    @27
    ctopon
    cfv
    wcel
    #
    cL
    @30
    ctopon
    cfv
    wcel
    #
    @3
    @31
    wph
    @32
    @3
    wph
    @24
    @25
    @32
    xkohmeo.x
    xkohmeo.y
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    adantr
    wph
    @33
    @3
    wph
    cL
    ctop
    wcel
    #
    @33
    xkohmeo.l
    cL
    @30
    @30
    eqid
    toptopon
    sylib
    #
    adantr
    wph
    @3
    simpr
    #
    @0
    @1
    cL
    @27
    @30
    cnf2
    syl3anc
    @27
    @30
    @0
    ffn
    syl
    vx
    vy
    cX
    cY
    @0
    fnov
    sylib
    #
    @36
    eqeltrrd
    cnmpt2k
    adantrr
    eqeltrd
    @22
    @0
    @26
    @18
    wph
    @3
    @29
    @10
    @37
    adantrr
    @22
    cX
    cX
    wceq
    cY
    cY
    wceq
    #
    @17
    @7
    wceq
    #
    vy
    cY
    wral
    #
    wa
    #
    vx
    cX
    wral
    @18
    @26
    wceq
    cX
    eqid
    @22
    @41
    vx
    cX
    wph
    @11
    vx
    wph
    vx
    nfv
    #
    @3
    @10
    vx
    @3
    vx
    nfv
    vx
    @4
    @9
    vx
    cX
    @8
    nfmpt1
    nfeq2
    nfan
    nfan
    @22
    @5
    cX
    wcel
    #
    @41
    @22
    @43
    wa
    #
    @40
    @38
    @44
    @39
    vy
    cY
    @22
    @43
    vy
    wph
    @11
    vy
    wph
    vy
    nfv
    #
    @3
    @10
    vy
    @3
    vy
    nfv
    vy
    @4
    @9
    vy
    vx
    cX
    @8
    vy
    cX
    nfcv
    vy
    cY
    @7
    nfmpt1
    nfmpt
    nfeq2
    nfan
    nfan
    @43
    vy
    nfv
    #
    nfan
    @22
    @43
    @6
    cY
    wcel
    #
    @39
    @22
    @43
    @47
    wa
    #
    wa
    #
    @17
    @6
    @8
    cfv
    #
    @7
    @49
    @6
    @16
    @8
    @49
    @16
    @5
    @9
    cfv
    #
    @8
    @49
    @5
    @4
    @9
    wph
    @3
    @10
    @48
    simplrr
    fveq1d
    @49
    @43
    @8
    cvv
    wcel
    #
    @51
    @8
    wceq
    @22
    @43
    @47
    simprl
    @49
    cY
    cK
    wcel
    #
    @52
    wph
    @53
    @11
    @48
    wph
    @25
    @53
    xkohmeo.y
    cY
    cK
    toponmax
    syl
    ad2antrr
    vy
    cY
    @7
    cK
    mptexg
    syl
    vx
    cX
    @8
    cvv
    @9
    @9
    eqid
    fvmpt2
    syl2anc
    eqtrd
    fveq1d
    @49
    @47
    @7
    cvv
    wcel
    @50
    @7
    wceq
    @22
    @43
    @47
    simprr
    @5
    @6
    @0
    ovex
    vy
    cY
    @7
    cvv
    @8
    @8
    eqid
    fvmpt2
    sylancl
    eqtrd
    expr
    ralrimi
    cY
    eqid
    #
    jctil
    ex
    ralrimi
    vx
    vy
    cX
    cY
    @17
    cX
    cY
    @7
    mpt2eq123
    sylancr
    eqtr4d
    jca
    wph
    @20
    wa
    #
    @3
    @10
    @55
    @0
    @18
    @2
    wph
    @15
    @19
    simprr
    #
    wph
    @15
    @18
    @2
    wcel
    @19
    wph
    @15
    wa
    #
    vx
    vy
    @17
    cJ
    cK
    cL
    cX
    cY
    @30
    wph
    @24
    @15
    xkohmeo.x
    adantr
    #
    wph
    @25
    @15
    xkohmeo.y
    adantr
    wph
    @33
    @15
    @35
    adantr
    wph
    cK
    ccmp
    cnlly
    wcel
    #
    @15
    xkohmeo.k
    adantr
    #
    @57
    @4
    vx
    cX
    vy
    cY
    @17
    cmpt
    #
    cmpt
    #
    @14
    @57
    @4
    vx
    cX
    @16
    cmpt
    @62
    @57
    vx
    cX
    cK
    cL
    ccn
    co
    #
    @4
    @57
    @24
    @13
    @63
    ctopon
    cfv
    wcel
    #
    @15
    cX
    @63
    @4
    wf
    @58
    @57
    cK
    ctop
    wcel
    #
    @34
    @64
    @57
    @59
    @65
    @60
    ccmp
    cK
    nllytop
    syl
    wph
    @34
    @15
    xkohmeo.l
    adantr
    cK
    cL
    @13
    @13
    eqid
    xkotopon
    syl2anc
    wph
    @15
    simpr
    #
    @4
    cJ
    @13
    cX
    @63
    cnf2
    syl3anc
    #
    feqmptd
    @57
    vx
    cX
    @16
    @61
    @57
    @43
    wa
    #
    vy
    cY
    @30
    @16
    @68
    @25
    @33
    @16
    @63
    wcel
    cY
    @30
    @16
    wf
    wph
    @25
    @15
    @43
    xkohmeo.y
    ad2antrr
    wph
    @33
    @15
    @43
    @35
    ad2antrr
    @57
    cX
    @63
    @5
    @4
    @67
    ffvelrnda
    @16
    cK
    cL
    cY
    @30
    cnf2
    syl3anc
    feqmptd
    mpteq2dva
    eqtrd
    #
    @66
    eqeltrrd
    cnmptk2
    adantrr
    eqeltrd
    @55
    @4
    @62
    @9
    wph
    @15
    @4
    @62
    wceq
    @19
    @69
    adantrr
    @55
    vx
    cX
    @8
    @61
    wph
    @20
    vx
    @42
    @15
    @19
    vx
    @15
    vx
    nfv
    vx
    @0
    @18
    vx
    vy
    cX
    cY
    @17
    nfmpt21
    nfeq2
    nfan
    nfan
    @55
    @43
    wa
    #
    @38
    @7
    @17
    wceq
    #
    vy
    cY
    wral
    @8
    @61
    wceq
    @54
    @70
    @71
    vy
    cY
    @55
    @43
    vy
    wph
    @20
    vy
    @45
    @15
    @19
    vy
    @15
    vy
    nfv
    vy
    @0
    @18
    vx
    vy
    cX
    cY
    @17
    nfmpt22
    nfeq2
    nfan
    nfan
    @46
    nfan
    @55
    @43
    @47
    @71
    @55
    @48
    @7
    @5
    @6
    @18
    co
    #
    @17
    @55
    @0
    @18
    @5
    @6
    @56
    oveqd
    @43
    @47
    @17
    cvv
    wcel
    @72
    @17
    wceq
    @6
    @16
    fvex
    vx
    vy
    cX
    cY
    @17
    @18
    cvv
    @18
    eqid
    ovmpt4g
    mp3an3
    sylan9eq
    expr
    ralrimi
    vy
    cY
    @7
    cY
    @17
    mpteq12
    sylancr
    mpteq2da
    eqtr4d
    jca
    impbida
    opabbidv
    @21
    @11
    vf
    vg
    copab
    #
    ccnv
    @12
    cF
    @73
    cF
    vf
    @2
    @9
    cmpt
    @73
    xkohmeo.f
    vf
    vg
    @2
    @9
    df-mpt
    eqtri
    cnveqi
    @11
    vf
    vg
    cnvopab
    eqtri
    vg
    vf
    @14
    @18
    df-mpt
    3eqtr4g
end
