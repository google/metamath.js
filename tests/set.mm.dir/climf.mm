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
include "nfv.mm"
include "nfeq2.mm"
include "nfan.mm"
include "fveq1.mm"
include "oveq12.mm"
include "sylan.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralbid.mm"
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
include "ralbidv.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem climf
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
  assume climf.nf: |- F/_ k F
  assume climf.f: |- ( ph -> F e. V )
  assume climf.fv: |- ( ( ph /\ k e. ZZ ) -> ( F ` k ) = B )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F j
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint A f
  disjoint A y
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint j y
  disjoint k y
  disjoint x y
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
    climf.f
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
    vx
    nfv
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
    @39
    @40
    vk
    vk
    @29
    cF
    climf.nf
    nfeq2
    @40
    vk
    nfv
    nfan
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
    ralbid
    rexbidv
    ralbid
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
    climf.fv
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
    climf.fv
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
