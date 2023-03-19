include "cv.mm"
include "cmpt2.mm"
include "co.mm"
include "cmpt.mm"
include "cxko.mm"
include "ccn.mm"
include "nfcv.mm"
include "nfmpt22.mm"
include "nfov.mm"
include "nfmpt.mm"
include "wceq.mm"
include "nfmpt21.mm"
include "oveq1.mm"
include "cbvmpt.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "simpr.mm"
include "simplr.mm"
include "wral.mm"
include "cxp.mm"
include "wf.mm"
include "ctx.mm"
include "ctopon.mm"
include "cfv.mm"
include "txtopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cntop2.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnmptcom.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt2.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "an32s.mm"
include "ovmpt4g.mm"
include "mpteq2dva.mm"
include "cop.mm"
include "xkoinjcn.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "cnmptk1.mm"

theorem cnmpt2k
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume cnmpt2k.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmpt2k.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmpt2k.a: |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )

  disjoint x y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint L v
  disjoint w x
  disjoint w y
  disjoint L w
  disjoint ph v
  disjoint ph w
  disjoint v z
  disjoint X v
  disjoint w z
  disjoint X w
  disjoint x z
  disjoint y z
  disjoint X z
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint A v
  disjoint A w
  disjoint A z
  disjoint J v
  disjoint J w
  disjoint J z
  disjoint K v
  disjoint K w
  disjoint K z
  assert |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )

  proof
    wph
    vw
    cX
    vv
    cY
    vv
    cv
    #
    vw
    cv
    #
    vy
    vx
    cY
    cX
    cA
    cmpt2
    #
    co
    #
    cmpt
    #
    cmpt
    #
    vx
    cX
    vy
    cY
    cA
    cmpt
    #
    cmpt
    #
    cJ
    cL
    cK
    cxko
    co
    ccn
    co
    wph
    @5
    vx
    cX
    vy
    cY
    vy
    cv
    #
    vx
    cv
    #
    @2
    co
    #
    cmpt
    #
    cmpt
    @7
    vw
    vx
    cX
    @4
    @11
    vx
    vv
    cY
    @3
    vx
    cY
    nfcv
    vx
    @0
    @1
    @2
    vx
    @0
    nfcv
    vy
    vx
    cY
    cX
    cA
    nfmpt22
    vx
    @1
    nfcv
    nfov
    nfmpt
    vw
    @11
    nfcv
    @1
    @9
    wceq
    #
    @4
    vy
    cY
    @8
    @1
    @2
    co
    #
    cmpt
    @11
    vv
    vy
    cY
    @3
    @13
    vy
    @0
    @1
    @2
    vy
    @0
    nfcv
    vy
    vx
    cY
    cX
    cA
    nfmpt21
    vy
    @1
    nfcv
    nfov
    vv
    @13
    nfcv
    @0
    @8
    @1
    @2
    oveq1
    cbvmpt
    @12
    vy
    cY
    @13
    @10
    @1
    @9
    @8
    @2
    oveq2
    mpteq2dv
    syl5eq
    cbvmpt
    wph
    vx
    cX
    @11
    @6
    wph
    @9
    cX
    wcel
    #
    wa
    #
    vy
    cY
    @10
    cA
    @15
    @8
    cY
    wcel
    #
    wa
    @16
    @14
    cA
    cL
    cuni
    #
    wcel
    #
    @10
    cA
    wceq
    @15
    @16
    simpr
    wph
    @14
    @16
    simplr
    wph
    @16
    @14
    @18
    wph
    @16
    wa
    @18
    vx
    cX
    wph
    @18
    vx
    cX
    wral
    #
    vy
    cY
    wph
    cY
    cX
    cxp
    #
    @17
    @2
    wf
    #
    @19
    vy
    cY
    wral
    wph
    cK
    cJ
    ctx
    co
    #
    @20
    ctopon
    cfv
    wcel
    #
    cL
    @17
    ctopon
    cfv
    wcel
    #
    @2
    @22
    cL
    ccn
    co
    #
    wcel
    @21
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @23
    cnmpt2k.k
    cnmpt2k.j
    cK
    cJ
    cY
    cX
    txtopon
    syl2anc
    #
    wph
    cL
    ctop
    wcel
    #
    @24
    wph
    vx
    vy
    cX
    cY
    cA
    cmpt2
    #
    cJ
    cK
    ctx
    co
    #
    cL
    ccn
    co
    wcel
    @29
    cnmpt2k.a
    @30
    @31
    cL
    cntop2
    syl
    cL
    @17
    @17
    eqid
    toptopon
    sylib
    wph
    vx
    vy
    cA
    cJ
    cK
    cL
    cX
    cY
    cnmpt2k.j
    cnmpt2k.k
    cnmpt2k.a
    cnmptcom
    #
    @2
    @22
    cL
    @20
    @17
    cnf2
    syl3anc
    #
    vy
    vx
    cY
    cX
    cA
    @17
    @2
    @2
    eqid
    #
    fmpt2
    sylibr
    r19.21bi
    r19.21bi
    an32s
    vy
    vx
    cY
    cX
    cA
    @2
    @17
    @34
    ovmpt4g
    syl3anc
    mpteq2dva
    mpteq2dva
    syl5eq
    wph
    vw
    vv
    vz
    @0
    @1
    cop
    #
    vz
    cv
    #
    @2
    cfv
    #
    @3
    cJ
    cK
    @22
    cL
    cX
    cY
    @20
    cnmpt2k.j
    cnmpt2k.k
    @28
    wph
    @27
    @26
    vw
    cX
    vv
    cY
    @35
    cmpt
    cmpt
    #
    cJ
    @22
    cK
    cxko
    co
    ccn
    co
    wcel
    cnmpt2k.j
    cnmpt2k.k
    vw
    vv
    cJ
    cK
    @38
    cX
    cY
    @38
    eqid
    xkoinjcn
    syl2anc
    wph
    @2
    vz
    @20
    @37
    cmpt
    @25
    wph
    vz
    @20
    @17
    @2
    @33
    feqmptd
    @32
    eqeltrrd
    @36
    @35
    wceq
    @37
    @35
    @2
    cfv
    @3
    @36
    @35
    @2
    fveq2
    @0
    @1
    @2
    df-ov
    syl6eqr
    cnmptk1
    eqeltrrd
end
