include "cioo.mm"
include "co.mm"
include "cmul.mm"
include "citg.mm"
include "caddc.mm"
include "cmin.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmpt.mm"
include "wf.mm"
include "wral.mm"
include "ccncf.mm"
include "cncff.mm"
include "syl.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "cicc.mm"
include "ioossicc.mm"
include "sseli.mm"
include "sylan2.mm"
include "mulcld.mm"
include "itgcl.mm"
include "pncan2d.mm"
include "itgadd.mm"
include "cr.mm"
include "cdv.mm"
include "cfv.mm"
include "fveq2.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfov.mm"
include "nffv.mm"
include "cbvitg.mm"
include "crn.mm"
include "ctg.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "tgioo2.mm"
include "cnt.mm"
include "wceq.mm"
include "iccntr.mm"
include "dvmptntr.mm"
include "cpr.mm"
include "reelprrecn.mm"
include "eqtr3d.mm"
include "dvmptmul.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "ctx.mm"
include "ccn.mm"
include "addcn.mm"
include "cres.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "rescncf.mm"
include "mpsyl.mm"
include "syl5eqelr.mm"
include "mulcncf.mm"
include "cncfmpt2f.mm"
include "eqeltrd.mm"
include "cibl.mm"
include "ibladd.mm"
include "ftc2.mm"
include "syl5eq.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "simpr.mm"
include "ovex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "itgeq2dv.mm"
include "csb.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ubicc2.mm"
include "syl3anc.mm"
include "csbex.mm"
include "fvmpts.mm"
include "csbied.mm"
include "lbicc2.mm"
include "oveq12d.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"

theorem itgparts
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cX: class X
  let cY: class Y
  let vt: setvar t
  assume itgparts.x: |- ( ph -> X e. RR )
  assume itgparts.y: |- ( ph -> Y e. RR )
  assume itgparts.le: |- ( ph -> X <_ Y )
  assume itgparts.a: |- ( ph -> ( x e. ( X [,] Y ) |-> A ) e. ( ( X [,] Y ) -cn-> CC ) )
  assume itgparts.c: |- ( ph -> ( x e. ( X [,] Y ) |-> C ) e. ( ( X [,] Y ) -cn-> CC ) )
  assume itgparts.b: |- ( ph -> ( x e. ( X (,) Y ) |-> B ) e. ( ( X (,) Y ) -cn-> CC ) )
  assume itgparts.d: |- ( ph -> ( x e. ( X (,) Y ) |-> D ) e. ( ( X (,) Y ) -cn-> CC ) )
  assume itgparts.ad: |- ( ph -> ( x e. ( X (,) Y ) |-> ( A x. D ) ) e. L^1 )
  assume itgparts.bc: |- ( ph -> ( x e. ( X (,) Y ) |-> ( B x. C ) ) e. L^1 )
  assume itgparts.da: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> A ) ) = ( x e. ( X (,) Y ) |-> B ) )
  assume itgparts.dc: |- ( ph -> ( RR _D ( x e. ( X [,] Y ) |-> C ) ) = ( x e. ( X (,) Y ) |-> D ) )
  assume itgparts.e: |- ( ( ph /\ x = X ) -> ( A x. C ) = E )
  assume itgparts.f: |- ( ( ph /\ x = Y ) -> ( A x. C ) = F )

  disjoint ph x
  disjoint X x
  disjoint Y x
  disjoint E x
  disjoint F x
  disjoint A t
  disjoint C t
  disjoint t x
  disjoint ph t
  disjoint X t
  disjoint Y t
  assert |- ( ph -> S. ( X (,) Y ) ( A x. D ) _d x = ( ( F - E ) - S. ( X (,) Y ) ( B x. C ) _d x ) )

  proof
    wph
    vx
    cX
    cY
    cioo
    co
    #
    cB
    cC
    cmul
    co
    #
    citg
    #
    vx
    @0
    cA
    cD
    cmul
    co
    #
    citg
    #
    caddc
    co
    #
    @2
    cmin
    co
    @4
    cF
    cE
    cmin
    co
    #
    @2
    cmin
    co
    wph
    @2
    @4
    wph
    vx
    @0
    @1
    cc
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    cB
    cC
    wph
    cB
    cc
    wcel
    #
    vx
    @0
    wph
    @0
    cc
    vx
    @0
    cB
    cmpt
    #
    wf
    #
    @10
    vx
    @0
    wral
    wph
    @11
    @0
    cc
    ccncf
    co
    #
    wcel
    @12
    itgparts.b
    @0
    cc
    @11
    cncff
    syl
    vx
    @0
    cc
    cB
    @11
    @11
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    @8
    wph
    @7
    cX
    cY
    cicc
    co
    #
    wcel
    #
    cC
    cc
    wcel
    #
    @0
    @15
    @7
    cX
    cY
    ioossicc
    #
    sseli
    #
    wph
    @17
    vx
    @15
    wph
    @15
    cc
    vx
    @15
    cC
    cmpt
    #
    wf
    #
    @17
    vx
    @15
    wral
    wph
    @20
    @15
    cc
    ccncf
    co
    #
    wcel
    #
    @21
    itgparts.c
    @15
    cc
    @20
    cncff
    syl
    vx
    @15
    cc
    cC
    @20
    @20
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    sylan2
    #
    mulcld
    #
    itgparts.bc
    itgcl
    wph
    vx
    @0
    @3
    cc
    @9
    cA
    cD
    @8
    wph
    @16
    cA
    cc
    wcel
    #
    @19
    wph
    @27
    vx
    @15
    wph
    @15
    cc
    vx
    @15
    cA
    cmpt
    #
    wf
    #
    @27
    vx
    @15
    wral
    wph
    @28
    @22
    wcel
    #
    @29
    itgparts.a
    @15
    cc
    @28
    cncff
    syl
    vx
    @15
    cc
    cA
    @28
    @28
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    sylan2
    #
    wph
    cD
    cc
    wcel
    #
    vx
    @0
    wph
    @0
    cc
    vx
    @0
    cD
    cmpt
    #
    wf
    #
    @33
    vx
    @0
    wral
    wph
    @34
    @13
    wcel
    @35
    itgparts.d
    @0
    cc
    @34
    cncff
    syl
    vx
    @0
    cc
    cD
    @34
    @34
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    mulcld
    #
    itgparts.ad
    itgcl
    pncan2d
    wph
    @5
    @6
    @2
    cmin
    wph
    vx
    @0
    @1
    @3
    caddc
    co
    #
    citg
    #
    @5
    @6
    wph
    vx
    @0
    @1
    @3
    cc
    @26
    itgparts.bc
    @37
    itgparts.ad
    itgadd
    wph
    vx
    @0
    @7
    cr
    vx
    @15
    cA
    cC
    cmul
    co
    #
    cmpt
    #
    cdv
    co
    #
    cfv
    #
    citg
    #
    cY
    @41
    cfv
    #
    cX
    @41
    cfv
    #
    cmin
    co
    #
    @39
    @6
    wph
    @44
    vt
    @0
    vt
    cv
    #
    @42
    cfv
    #
    citg
    @47
    vx
    vt
    @0
    @43
    @49
    @7
    @48
    @42
    fveq2
    vt
    @43
    nfcv
    vx
    @48
    @42
    vx
    cr
    @41
    cdv
    vx
    cr
    nfcv
    vx
    cdv
    nfcv
    vx
    @15
    @40
    nfmpt1
    nfov
    vx
    @48
    nfcv
    nffv
    cbvitg
    wph
    vt
    cX
    cY
    @41
    itgparts.x
    itgparts.y
    itgparts.le
    wph
    @42
    vx
    @0
    @38
    cmpt
    #
    @13
    wph
    @42
    cr
    vx
    @0
    @40
    cmpt
    cdv
    co
    vx
    @0
    @1
    cD
    cA
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    @50
    wph
    vx
    @40
    cr
    cioo
    crn
    ctg
    cfv
    #
    ccnfld
    ctopn
    cfv
    #
    @15
    @0
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    #
    wph
    cX
    cr
    wcel
    #
    cY
    cr
    wcel
    #
    @15
    cr
    wss
    itgparts.x
    itgparts.y
    cX
    cY
    iccssre
    syl2anc
    #
    wph
    @16
    wa
    cA
    cC
    @31
    @24
    mulcld
    @54
    @54
    eqid
    #
    tgioo2
    #
    @59
    wph
    @56
    @57
    @15
    @53
    cnt
    cfv
    cfv
    @0
    wceq
    itgparts.x
    itgparts.y
    cX
    cY
    iccntr
    syl2anc
    #
    dvmptntr
    wph
    vx
    cA
    cB
    cC
    cD
    cr
    cc
    cc
    @0
    cr
    cr
    cc
    cpr
    wcel
    wph
    reelprrecn
    a1i
    @32
    @14
    wph
    cr
    @28
    cdv
    co
    cr
    vx
    @0
    cA
    cmpt
    #
    cdv
    co
    @11
    wph
    vx
    cA
    cr
    @53
    @54
    @15
    @0
    @55
    @58
    @31
    @60
    @59
    @61
    dvmptntr
    itgparts.da
    eqtr3d
    @25
    @36
    wph
    cr
    @20
    cdv
    co
    cr
    vx
    @0
    cC
    cmpt
    #
    cdv
    co
    @34
    wph
    vx
    cC
    cr
    @53
    @54
    @15
    @0
    @55
    @58
    @24
    @60
    @59
    @61
    dvmptntr
    itgparts.dc
    eqtr3d
    dvmptmul
    wph
    vx
    @0
    @52
    @38
    @9
    @51
    @3
    @1
    caddc
    @9
    cD
    cA
    @36
    @32
    mulcomd
    oveq2d
    mpteq2dva
    3eqtrd
    #
    wph
    vx
    @1
    @3
    caddc
    @54
    @0
    @59
    caddc
    @54
    @54
    ctx
    co
    @54
    ccn
    co
    wcel
    wph
    @54
    @59
    addcn
    a1i
    wph
    vx
    cB
    cC
    @0
    itgparts.b
    wph
    @63
    @20
    @0
    cres
    #
    @13
    @0
    @15
    wss
    #
    @65
    @63
    wceq
    @18
    vx
    @15
    @0
    cC
    resmpt
    ax-mp
    @66
    wph
    @23
    @65
    @13
    wcel
    @18
    itgparts.c
    @15
    cc
    @0
    @20
    rescncf
    mpsyl
    syl5eqelr
    mulcncf
    wph
    vx
    cA
    cD
    @0
    wph
    @62
    @28
    @0
    cres
    #
    @13
    @66
    @67
    @62
    wceq
    @18
    vx
    @15
    @0
    cA
    resmpt
    ax-mp
    @66
    wph
    @30
    @67
    @13
    wcel
    @18
    itgparts.a
    @15
    cc
    @0
    @28
    rescncf
    mpsyl
    syl5eqelr
    itgparts.d
    mulcncf
    cncfmpt2f
    eqeltrd
    wph
    @42
    @50
    cibl
    @64
    wph
    vx
    @0
    @1
    @3
    cc
    @26
    itgparts.bc
    @37
    itgparts.ad
    ibladd
    eqeltrd
    wph
    vx
    cA
    cC
    @15
    itgparts.a
    itgparts.c
    mulcncf
    ftc2
    syl5eq
    wph
    vx
    @0
    @43
    @38
    @9
    @43
    @7
    @50
    cfv
    #
    @38
    wph
    @43
    @68
    wceq
    @8
    wph
    @7
    @42
    @50
    @64
    fveq1d
    adantr
    @9
    @8
    @38
    cvv
    wcel
    @68
    @38
    wceq
    wph
    @8
    simpr
    @1
    @3
    caddc
    ovex
    vx
    @0
    @38
    cvv
    @50
    @50
    eqid
    fvmpt2
    sylancl
    eqtrd
    itgeq2dv
    wph
    @45
    cF
    @46
    cE
    cmin
    wph
    @45
    vx
    cY
    @40
    csb
    #
    cF
    wph
    cY
    @15
    wcel
    #
    @69
    cvv
    wcel
    @45
    @69
    wceq
    wph
    cX
    cxr
    wcel
    #
    cY
    cxr
    wcel
    #
    cX
    cY
    cle
    wbr
    #
    @70
    wph
    cX
    itgparts.x
    rexrd
    #
    wph
    cY
    itgparts.y
    rexrd
    #
    itgparts.le
    cX
    cY
    ubicc2
    syl3anc
    vx
    cY
    @40
    cA
    cC
    cmul
    ovex
    #
    csbex
    vx
    cY
    @40
    @15
    @41
    cvv
    @41
    eqid
    #
    fvmpts
    sylancl
    wph
    vx
    cY
    @40
    cF
    cr
    itgparts.y
    itgparts.f
    csbied
    eqtrd
    wph
    @46
    vx
    cX
    @40
    csb
    #
    cE
    wph
    cX
    @15
    wcel
    #
    @78
    cvv
    wcel
    @46
    @78
    wceq
    wph
    @71
    @72
    @73
    @79
    @74
    @75
    itgparts.le
    cX
    cY
    lbicc2
    syl3anc
    vx
    cX
    @40
    @76
    csbex
    vx
    cX
    @40
    @15
    @41
    cvv
    @77
    fvmpts
    sylancl
    wph
    vx
    cX
    @40
    cE
    cr
    itgparts.x
    itgparts.e
    csbied
    eqtrd
    oveq12d
    3eqtr3d
    eqtr3d
    oveq1d
    eqtr3d
end
