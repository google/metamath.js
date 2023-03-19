include "climc.mm"
include "co.mm"
include "wcel.mm"
include "cc.mm"
include "cv.mm"
include "wne.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "c1.mm"
include "1rp.mm"
include "a1i.mm"
include "cc0.mm"
include "wceq.mm"
include "csb.mm"
include "simpr.mm"
include "cvv.mm"
include "wnfc.mm"
include "vex.mm"
include "nfcv.mm"
include "csbtt.mm"
include "mp2an.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "subidd.mm"
include "abs0.mm"
include "3eqtrd.mm"
include "adantlr.mm"
include "rpgt0.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "fmptd.mm"
include "ellimc3.mm"
include "mpbir2and.mm"

theorem constlimc
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume constlimc.f: |- F = ( x e. A |-> B )
  assume constlimc.a: |- ( ph -> A C_ CC )
  assume constlimc.b: |- ( ph -> B e. CC )
  assume constlimc.c: |- ( ph -> C e. CC )

  disjoint A x
  disjoint B x
  disjoint ph x
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint F v
  disjoint F w
  disjoint F y
  disjoint ph v
  disjoint ph w
  disjoint ph y
  assert |- ( ph -> B e. ( F limCC C ) )

  proof
    wph
    cB
    cF
    cC
    climc
    co
    wcel
    cB
    cc
    wcel
    #
    vv
    cv
    #
    cC
    wne
    #
    @1
    cC
    cmin
    co
    cabs
    cfv
    #
    vw
    cv
    #
    clt
    wbr
    #
    wa
    #
    @1
    cF
    cfv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vv
    cA
    wral
    #
    vw
    crp
    wrex
    #
    vy
    crp
    wral
    constlimc.b
    wph
    @14
    vy
    crp
    wph
    @10
    crp
    wcel
    #
    wa
    #
    c1
    crp
    wcel
    #
    @2
    @3
    c1
    clt
    wbr
    #
    wa
    #
    @11
    wi
    #
    vv
    cA
    wral
    #
    @14
    @17
    @16
    1rp
    a1i
    @16
    @20
    vv
    cA
    @16
    @1
    cA
    wcel
    #
    wa
    #
    @11
    @19
    @23
    @9
    cc0
    @10
    clt
    wph
    @22
    @9
    cc0
    wceq
    @15
    wph
    @22
    wa
    #
    @9
    cB
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cc0
    cabs
    cfv
    #
    cc0
    @24
    @8
    @25
    cabs
    @24
    @8
    vx
    @1
    cB
    csb
    #
    cB
    cmin
    co
    @25
    @24
    @7
    @28
    cB
    cmin
    @24
    @22
    @28
    cc
    wcel
    #
    @7
    @28
    wceq
    wph
    @22
    simpr
    wph
    @29
    @22
    wph
    @28
    cB
    cc
    @1
    cvv
    wcel
    vx
    cB
    wnfc
    @28
    cB
    wceq
    vv
    vex
    vx
    cB
    nfcv
    vx
    @1
    cB
    cvv
    csbtt
    mp2an
    #
    constlimc.b
    syl5eqel
    adantr
    vx
    @1
    cB
    cA
    cF
    cc
    constlimc.f
    fvmpts
    syl2anc
    oveq1d
    @28
    cB
    cB
    cmin
    @30
    oveq1i
    syl6eq
    fveq2d
    wph
    @26
    @27
    wceq
    @22
    wph
    @25
    cc0
    cabs
    wph
    cB
    constlimc.b
    subidd
    fveq2d
    adantr
    @27
    cc0
    wceq
    @24
    abs0
    a1i
    3eqtrd
    adantlr
    @15
    cc0
    @10
    clt
    wbr
    wph
    @22
    @10
    rpgt0
    ad2antlr
    eqbrtrd
    a1d
    ralrimiva
    @13
    @21
    vw
    c1
    crp
    @4
    c1
    wceq
    #
    @12
    @20
    vv
    cA
    @31
    @6
    @19
    @11
    @31
    @5
    @18
    @2
    @4
    c1
    @3
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimiva
    wph
    vy
    vw
    vv
    cA
    cC
    cB
    cF
    wph
    vx
    cA
    cB
    cc
    cF
    wph
    @0
    vx
    cv
    cA
    wcel
    constlimc.b
    adantr
    constlimc.f
    fmptd
    constlimc.a
    constlimc.c
    ellimc3
    mpbir2and
end
