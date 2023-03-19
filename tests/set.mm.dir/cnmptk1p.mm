include "cmpt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wf.mm"
include "wral.mm"
include "ctopon.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "eqid.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "adantr.mm"
include "cxko.mm"
include "ctop.mm"
include "ccmp.mm"
include "cnlly.mm"
include "nllytop.mm"
include "syl.mm"
include "topontop.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "mpteq2dva.mm"
include "cmpt2.mm"
include "cuni.mm"
include "ctx.mm"
include "toponuni.mm"
include "mpt2eq12.mm"
include "sylancr.mm"
include "xkofvcn.mm"
include "eqeltrd.mm"
include "fveq1.mm"
include "fveq2.mm"
include "sylan9eq.mm"
include "cnmpt12.mm"
include "eqeltrrd.mm"

theorem cnmptk1p
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
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
  assume cnmptk1p.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1p.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptk1p.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmptk1p.n: |- ( ph -> K e. N-Locally Comp )
  assume cnmptk1p.a: |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )
  assume cnmptk1p.b: |- ( ph -> ( x e. X |-> B ) e. ( J Cn K ) )
  assume cnmptk1p.c: |- ( y = B -> A = C )

  disjoint J x
  disjoint K x
  disjoint L x
  disjoint B y
  disjoint C y
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
  disjoint B z
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
  assert |- ( ph -> ( x e. X |-> C ) e. ( J Cn L ) )

  proof
    wph
    vx
    cX
    cB
    vy
    cY
    cA
    cmpt
    #
    cfv
    #
    cmpt
    vx
    cX
    cC
    cmpt
    cJ
    cL
    ccn
    co
    wph
    vx
    cX
    @1
    cC
    wph
    vx
    cv
    cX
    wcel
    #
    wa
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    @1
    cC
    wceq
    wph
    @4
    vx
    cX
    wph
    cX
    cY
    vx
    cX
    cB
    cmpt
    #
    wf
    #
    @4
    vx
    cX
    wral
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @6
    cJ
    cK
    ccn
    co
    wcel
    @7
    cnmptk1p.j
    cnmptk1p.k
    cnmptk1p.b
    @6
    cJ
    cK
    cX
    cY
    cnf2
    syl3anc
    vx
    cX
    cY
    cB
    @6
    @6
    eqid
    fmpt
    sylibr
    r19.21bi
    #
    @3
    @4
    cA
    cZ
    wcel
    #
    vy
    cY
    wral
    #
    @5
    @10
    @3
    cY
    cZ
    @0
    wf
    #
    @12
    @3
    @9
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @0
    cK
    cL
    ccn
    co
    #
    wcel
    #
    @13
    wph
    @9
    @2
    cnmptk1p.k
    adantr
    wph
    @14
    @2
    cnmptk1p.l
    adantr
    wph
    @16
    vx
    cX
    wph
    cX
    @15
    vx
    cX
    @0
    cmpt
    #
    wf
    #
    @16
    vx
    cX
    wral
    wph
    @8
    cL
    cK
    cxko
    co
    #
    @15
    ctopon
    cfv
    wcel
    #
    @17
    cJ
    @19
    ccn
    co
    wcel
    @18
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
    @20
    wph
    cK
    ccmp
    cnlly
    wcel
    #
    @21
    cnmptk1p.n
    ccmp
    cK
    nllytop
    syl
    wph
    @14
    @22
    cnmptk1p.l
    cZ
    cL
    topontop
    syl
    #
    cK
    cL
    @19
    @19
    eqid
    xkotopon
    syl2anc
    #
    cnmptk1p.a
    @17
    cJ
    @19
    cX
    @15
    cnf2
    syl3anc
    vx
    cX
    @15
    @0
    @17
    @17
    eqid
    fmpt
    sylibr
    r19.21bi
    @0
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
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    @11
    @5
    vy
    cB
    cY
    vy
    cv
    cB
    wceq
    cA
    cC
    cZ
    cnmptk1p.c
    eleq1d
    rspcv
    sylc
    vy
    cB
    cA
    cC
    cY
    cZ
    @0
    cnmptk1p.c
    @26
    fvmptg
    syl2anc
    mpteq2dva
    wph
    vx
    vf
    vz
    @0
    cB
    vz
    cv
    #
    vf
    cv
    #
    cfv
    #
    @1
    cJ
    @19
    cK
    cL
    cX
    @15
    cY
    cnmptk1p.j
    cnmptk1p.a
    cnmptk1p.b
    @25
    cnmptk1p.k
    wph
    vf
    vz
    @15
    cY
    @29
    cmpt2
    #
    vf
    vz
    @15
    cK
    cuni
    #
    @29
    cmpt2
    #
    @19
    cK
    ctx
    co
    cL
    ccn
    co
    #
    wph
    @15
    @15
    wceq
    cY
    @31
    wceq
    #
    @30
    @32
    wceq
    @15
    eqid
    wph
    @9
    @34
    cnmptk1p.k
    cY
    cK
    toponuni
    syl
    vf
    vz
    @15
    cY
    @15
    @31
    @29
    mpt2eq12
    sylancr
    wph
    @23
    @22
    @32
    @33
    wcel
    cnmptk1p.n
    @24
    vz
    cK
    cL
    vf
    @32
    @31
    @31
    eqid
    @32
    eqid
    xkofvcn
    syl2anc
    eqeltrd
    @28
    @0
    wceq
    @27
    cB
    wceq
    @29
    @27
    @0
    cfv
    @1
    @27
    @28
    @0
    fveq1
    @27
    cB
    @0
    fveq2
    sylan9eq
    cnmpt12
    eqeltrrd
end
