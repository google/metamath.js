include "cmpt.mm"
include "cfv.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "wceq.mm"
include "adantr.mm"
include "wral.mm"
include "wf.mm"
include "ctopon.mm"
include "ctop.mm"
include "topontop.mm"
include "syl.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cxko.mm"
include "xkotopon.mm"
include "syl2anc.mm"
include "cnf2.mm"
include "syl3anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "fvmptg.mm"
include "mpteq2dva.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "xkopjcn.mm"
include "fveq1.mm"
include "cnmpt11.mm"
include "eqeltrrd.mm"

theorem cnmptkp
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
  let vw: setvar w
  let cM: class M
  let vz: setvar z
  assume cnmptk1.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume cnmptk1.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume cnmptk1.l: |- ( ph -> L e. ( TopOn ` Z ) )
  assume cnmptkp.a: |- ( ph -> ( x e. X |-> ( y e. Y |-> A ) ) e. ( J Cn ( L ^ko K ) ) )
  assume cnmptkp.b: |- ( ph -> B e. Y )
  assume cnmptkp.c: |- ( y = B -> A = C )

  disjoint B y
  disjoint C y
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint Z x
  disjoint Z y
  disjoint B x
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint K w
  disjoint L w
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint w z
  disjoint Z w
  disjoint x z
  disjoint y z
  disjoint Z z
  disjoint A w
  disjoint A z
  disjoint B w
  disjoint ph w
  disjoint X w
  disjoint Y w
  disjoint C z
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
    cL
    cuni
    #
    wcel
    #
    @1
    cC
    wceq
    wph
    @4
    @2
    cnmptkp.b
    adantr
    #
    @3
    @4
    cA
    @5
    wcel
    #
    vy
    cY
    wral
    #
    @6
    @7
    @3
    cY
    @5
    @0
    wf
    #
    @9
    @3
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cL
    @5
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
    @10
    wph
    @11
    @2
    cnmptk1.k
    adantr
    @3
    cL
    ctop
    wcel
    #
    @12
    wph
    @15
    @2
    wph
    cL
    cZ
    ctopon
    cfv
    wcel
    @15
    cnmptk1.l
    cZ
    cL
    topontop
    syl
    #
    adantr
    cL
    @5
    @5
    eqid
    toptopon
    sylib
    wph
    @14
    vx
    cX
    wph
    cX
    @13
    vx
    cX
    @0
    cmpt
    #
    wf
    #
    @14
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
    @13
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
    cnmptk1.j
    wph
    cK
    ctop
    wcel
    #
    @15
    @20
    wph
    @11
    @21
    cnmptk1.k
    cY
    cK
    topontop
    syl
    #
    @16
    cK
    cL
    @19
    @19
    eqid
    xkotopon
    syl2anc
    #
    cnmptkp.a
    @17
    cJ
    @19
    cX
    @13
    cnf2
    syl3anc
    vx
    cX
    @13
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
    @5
    cnf2
    syl3anc
    vy
    cY
    @5
    cA
    @0
    @0
    eqid
    #
    fmpt
    sylibr
    @8
    @6
    vy
    cB
    cY
    vy
    cv
    cB
    wceq
    cA
    cC
    @5
    cnmptkp.c
    eleq1d
    rspcv
    sylc
    vy
    cB
    cA
    cC
    cY
    @5
    @0
    cnmptkp.c
    @24
    fvmptg
    syl2anc
    mpteq2dva
    wph
    vx
    vw
    @0
    cB
    vw
    cv
    #
    cfv
    #
    @1
    cJ
    @19
    cL
    cX
    @13
    cnmptk1.j
    cnmptkp.a
    @23
    wph
    @21
    @15
    cB
    cK
    cuni
    #
    wcel
    vw
    @13
    @26
    cmpt
    @19
    cL
    ccn
    co
    wcel
    @22
    @16
    wph
    cB
    cY
    @27
    cnmptkp.b
    wph
    @11
    cY
    @27
    wceq
    cnmptk1.k
    cY
    cK
    toponuni
    syl
    eleqtrd
    cB
    cK
    cL
    vw
    @27
    @27
    eqid
    xkopjcn
    syl3anc
    cB
    @25
    @0
    fveq1
    cnmpt11
    eqeltrrd
end
