include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "cvv.mm"
include "wi.mm"
include "climrel.mm"
include "brrelex2i.mm"
include "a1i.mm"
include "elex.mm"
include "adantr.mm"
include "wb.mm"
include "wceq.mm"
include "simpr.mm"
include "eleq1d.mm"
include "fveq1.mm"
include "oveq12.mm"
include "sylan.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "df-clim.mm"
include "brabga.mm"
include "ex.mm"
include "syl.mm"
include "pm5.21ndd.mm"
include "eluzelz.mm"
include "oveq1d.mm"
include "sylan2.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem clim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cV: class V
  let vf: setvar f
  let vy: setvar y
  assume clim.1: |- ( ph -> F e. V )
  assume clim.3: |- ( ( ph /\ k e. ZZ ) -> ( F ` k ) = B )

  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint A y
  disjoint F f
  disjoint F y
  assert |- ( ph -> ( F ~~> A <-> ( A e. CC /\ A. x e. RR+ E. j e. ZZ A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` ( B - A ) ) < x ) ) ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    #
    cA
    cc
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @3
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    @1
    cB
    cc
    wcel
    #
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vk
    @11
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    cA
    cvv
    wcel
    #
    @0
    @15
    @0
    @24
    wi
    wph
    cF
    cA
    cli
    climrel
    brrelex2i
    a1i
    @15
    @24
    wi
    wph
    @1
    @24
    @14
    cA
    cc
    elex
    adantr
    a1i
    wph
    cF
    cV
    wcel
    #
    @24
    @0
    @15
    wb
    #
    wi
    clim.1
    @25
    @24
    @26
    vy
    cv
    #
    cc
    wcel
    #
    @2
    vf
    cv
    #
    cfv
    #
    cc
    wcel
    #
    @30
    @27
    cmin
    co
    #
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    wa
    #
    vk
    @11
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    wa
    @15
    vf
    vy
    cF
    cA
    cli
    cV
    cvv
    @29
    cF
    wceq
    #
    @27
    cA
    wceq
    #
    wa
    #
    @28
    @1
    @38
    @14
    @41
    @27
    cA
    cc
    @39
    @40
    simpr
    eleq1d
    @41
    @37
    @13
    vx
    crp
    @41
    @36
    @12
    vj
    cz
    @41
    @35
    @9
    vk
    @11
    @41
    @31
    @4
    @34
    @8
    @41
    @30
    @3
    cc
    @39
    @30
    @3
    wceq
    #
    @40
    @2
    @29
    cF
    fveq1
    #
    adantr
    eleq1d
    @41
    @33
    @6
    @7
    clt
    @41
    @32
    @5
    cabs
    @39
    @42
    @40
    @32
    @5
    wceq
    @43
    @30
    @3
    @27
    cA
    cmin
    oveq12
    sylan
    fveq2d
    breq1d
    anbi12d
    ralbidv
    rexbidv
    ralbidv
    anbi12d
    vx
    vy
    vf
    vj
    vk
    df-clim
    brabga
    ex
    syl
    pm5.21ndd
    wph
    @14
    @23
    @1
    wph
    @13
    @22
    vx
    crp
    wph
    @12
    @21
    vj
    cz
    wph
    @9
    @20
    vk
    @11
    @2
    @11
    wcel
    wph
    @2
    cz
    wcel
    #
    @9
    @20
    wb
    @10
    @2
    eluzelz
    wph
    @44
    wa
    #
    @4
    @16
    @8
    @19
    @45
    @3
    cB
    cc
    clim.3
    eleq1d
    @45
    @6
    @18
    @7
    clt
    @45
    @5
    @17
    cabs
    @45
    @3
    cB
    cA
    cmin
    clim.3
    oveq1d
    fveq2d
    breq1d
    anbi12d
    sylan2
    ralbidva
    rexbidv
    ralbidv
    anbi2d
    bitrd
end
