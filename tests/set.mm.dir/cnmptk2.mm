include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cmpt2.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfmpt1.mm"
include "nfmpt.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "sylan9eq.mm"
include "cbvmpt2.mm"
include "wcel.mm"
include "wa.mm"
include "simplr.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "cxko.mm"
include "ctop.mm"
include "ccmp.mm"
include "cnlly.mm"
include "nllytop.mm"
include "syl.mm"
include "topontop.mm"
include "eqid.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "fvmpt2.mm"
include "simpr.mm"
include "eqtrd.mm"
include "3impa.mm"
include "mpt2eq3dva.mm"
include "syl5eq.mm"
include "cnmpt1st.mm"
include "cnmpt21f.mm"
include "cnmpt2nd.mm"
include "cuni.mm"
include "toponuni.mm"
include "mpt2eq12.mm"
include "sylancr.mm"
include "xkofvcn.mm"
include "eqeltrd.mm"
include "fveq1.mm"
include "cnmpt22.mm"
include "eqeltrrd.mm"

theorem cnmptk2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let cC: class C
  assume cnmptk1p.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1p.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptk1p.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmptk1p.n: |- ( ph -> K e. N-Locally Comp )
  assume cnmptk2.a: |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )

  disjoint J x
  disjoint K x
  disjoint L x
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint ph y
  disjoint Z y
  disjoint f k
  disjoint f w
  disjoint f z
  disjoint A f
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint f x
  disjoint J f
  disjoint k x
  disjoint J k
  disjoint w x
  disjoint J w
  disjoint x z
  disjoint J z
  disjoint K f
  disjoint K k
  disjoint K w
  disjoint K z
  disjoint L f
  disjoint L k
  disjoint L w
  disjoint L z
  disjoint f y
  disjoint B f
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint X f
  disjoint k y
  disjoint X k
  disjoint w y
  disjoint X w
  disjoint X z
  disjoint Y f
  disjoint Y k
  disjoint Y w
  disjoint Y z
  disjoint f ph
  disjoint k ph
  disjoint ph w
  disjoint ph z
  assert |- ( ph -> ( x e. X , y e. Y |-> A ) e. ( ( J tX K ) Cn L ) )

  proof
    wph
    vw
    vk
    cX
    cY
    vk
    cv
    #
    vw
    cv
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
    cfv
    #
    cfv
    #
    cmpt2
    #
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
    cL
    ccn
    co
    wph
    @6
    vx
    vy
    cX
    cY
    vy
    cv
    #
    vx
    cv
    #
    @3
    cfv
    #
    cfv
    #
    cmpt2
    @7
    vw
    vk
    vx
    vy
    cX
    cY
    @5
    @11
    vx
    @0
    @4
    vx
    cX
    @2
    @1
    nffvmpt1
    vx
    @0
    nfcv
    nffv
    vy
    @0
    @4
    vy
    @1
    @3
    vy
    vx
    cX
    @2
    vy
    cX
    nfcv
    vy
    cY
    cA
    nfmpt1
    nfmpt
    vy
    @1
    nfcv
    nffv
    vy
    @0
    nfcv
    nffv
    vw
    @11
    nfcv
    vk
    @11
    nfcv
    @1
    @9
    wceq
    #
    @0
    @8
    wceq
    @5
    @0
    @10
    cfv
    @11
    @12
    @0
    @4
    @10
    @1
    @9
    @3
    fveq2
    fveq1d
    @0
    @8
    @10
    fveq2
    sylan9eq
    cbvmpt2
    wph
    vx
    vy
    cX
    cY
    @11
    cA
    wph
    @9
    cX
    wcel
    #
    @8
    cY
    wcel
    #
    @11
    cA
    wceq
    wph
    @13
    wa
    #
    @14
    wa
    #
    @11
    @8
    @2
    cfv
    #
    cA
    @16
    @8
    @10
    @2
    @16
    @13
    @2
    cK
    cL
    ccn
    co
    #
    wcel
    #
    @10
    @2
    wceq
    wph
    @13
    @14
    simplr
    @15
    @19
    @14
    wph
    @19
    vx
    cX
    wph
    cX
    @18
    @3
    wf
    #
    @19
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    cL
    cK
    cxko
    co
    #
    @18
    ctopon
    cfv
    wcel
    #
    @3
    cJ
    @21
    ccn
    co
    wcel
    @20
    cnmptk1p.j
    wph
    cK
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    @22
    wph
    cK
    ccmp
    cnlly
    wcel
    #
    @23
    cnmptk1p.n
    ccmp
    cK
    nllytop
    syl
    wph
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @24
    cnmptk1p.l
    cZ
    cL
    topontop
    syl
    #
    cK
    cL
    @21
    @21
    eqid
    xkotopon
    syl2anc
    #
    cnmptk2.a
    @3
    cJ
    @21
    cX
    @18
    cnf2
    syl3anc
    vx
    cX
    @18
    @2
    @3
    @3
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    #
    adantr
    vx
    cX
    @2
    @18
    @3
    @29
    fvmpt2
    syl2anc
    fveq1d
    @16
    @14
    cA
    cZ
    wcel
    #
    @17
    cA
    wceq
    @15
    @14
    simpr
    @15
    @31
    vy
    cY
    @15
    cY
    cZ
    @2
    wf
    #
    @31
    vy
    cY
    wral
    @15
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @26
    @19
    @32
    wph
    @33
    @13
    cnmptk1p.k
    adantr
    wph
    @26
    @13
    cnmptk1p.l
    adantr
    @30
    @2
    cK
    cL
    cY
    cZ
    cnf2
    syl3anc
    vy
    cY
    cZ
    cA
    @2
    @2
    eqid
    #
    fmpt
    sylibr
    r19.21bi
    vy
    cY
    cA
    cZ
    @2
    @34
    fvmpt2
    syl2anc
    eqtrd
    3impa
    mpt2eq3dva
    syl5eq
    wph
    vw
    vk
    vf
    vz
    @4
    @0
    vz
    cv
    #
    vf
    cv
    #
    cfv
    #
    @5
    cJ
    cK
    @21
    cK
    cL
    cY
    cX
    cY
    @18
    cnmptk1p.j
    cnmptk1p.k
    wph
    vw
    vk
    @1
    @3
    cJ
    cK
    cJ
    @21
    cX
    cY
    cnmptk1p.j
    cnmptk1p.k
    wph
    vw
    vk
    cJ
    cK
    cX
    cY
    cnmptk1p.j
    cnmptk1p.k
    cnmpt1st
    cnmptk2.a
    cnmpt21f
    wph
    vw
    vk
    cJ
    cK
    cX
    cY
    cnmptk1p.j
    cnmptk1p.k
    cnmpt2nd
    @28
    cnmptk1p.k
    wph
    vf
    vz
    @18
    cY
    @37
    cmpt2
    #
    vf
    vz
    @18
    cK
    cuni
    #
    @37
    cmpt2
    #
    @21
    cK
    ctx
    co
    cL
    ccn
    co
    #
    wph
    @18
    @18
    wceq
    cY
    @39
    wceq
    #
    @38
    @40
    wceq
    @18
    eqid
    wph
    @33
    @42
    cnmptk1p.k
    cY
    cK
    toponuni
    syl
    vf
    vz
    @18
    cY
    @18
    @39
    @37
    mpt2eq12
    sylancr
    wph
    @25
    @24
    @40
    @41
    wcel
    cnmptk1p.n
    @27
    vz
    cK
    cL
    vf
    @40
    @39
    @39
    eqid
    @40
    eqid
    xkofvcn
    syl2anc
    eqeltrd
    @36
    @4
    wceq
    @35
    @0
    wceq
    @37
    @35
    @4
    cfv
    @5
    @35
    @36
    @4
    fveq1
    @35
    @0
    @4
    fveq2
    sylan9eq
    cnmpt22
    eqeltrrd
end
