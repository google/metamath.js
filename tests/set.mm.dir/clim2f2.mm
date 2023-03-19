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
include "eqidd.mm"
include "climf2.mm"
include "nfv.mm"
include "nfan.mm"
include "wb.mm"
include "uztrn2.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbida.mm"
include "rexbidva.mm"
include "rexuz3.mm"
include "syl.mm"
include "bitr3d.mm"
include "ralbidv.mm"
include "anbi2d.mm"
include "bitr4d.mm"

theorem clim2f2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume clim2f2.p: |- F/ k ph
  assume clim2f2.k: |- F/_ k F
  assume clim2f2.z: |- Z = ( ZZ>= ` M )
  assume clim2f2.m: |- ( ph -> M e. ZZ )
  assume clim2f2.f: |- ( ph -> F e. V )
  assume clim2f2.b: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F j
  disjoint F x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint ph x
  assert |- ( ph -> ( F ~~> A <-> ( A e. CC /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` ( B - A ) ) < x ) ) ) )

  proof
    wph
    cF
    cA
    cli
    wbr
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
    @2
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
    @0
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
    @6
    clt
    wbr
    #
    wa
    #
    vk
    @10
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    wa
    wph
    vx
    cA
    @2
    vj
    vk
    cF
    cV
    clim2f2.p
    clim2f2.k
    clim2f2.f
    wph
    @1
    cz
    wcel
    wa
    @2
    eqidd
    climf2
    wph
    @21
    @13
    @0
    wph
    @20
    @12
    vx
    crp
    wph
    @11
    vj
    cZ
    wrex
    #
    @20
    @12
    wph
    @11
    @19
    vj
    cZ
    wph
    @9
    cZ
    wcel
    #
    wa
    @8
    @18
    vk
    @10
    wph
    @23
    vk
    clim2f2.p
    @23
    vk
    nfv
    nfan
    wph
    @23
    @1
    @10
    wcel
    #
    @8
    @18
    wb
    #
    @23
    @24
    wa
    wph
    @1
    cZ
    wcel
    #
    @25
    cM
    @1
    @9
    cZ
    clim2f2.z
    uztrn2
    wph
    @26
    wa
    #
    @3
    @14
    @7
    @17
    @27
    @2
    cB
    cc
    clim2f2.b
    eleq1d
    @27
    @5
    @16
    @6
    clt
    @27
    @4
    @15
    cabs
    @27
    @2
    cB
    cA
    cmin
    clim2f2.b
    oveq1d
    fveq2d
    breq1d
    anbi12d
    sylan2
    anassrs
    ralbida
    rexbidva
    wph
    cM
    cz
    wcel
    @22
    @12
    wb
    clim2f2.m
    @8
    vj
    vk
    cM
    cZ
    clim2f2.z
    rexuz3
    syl
    bitr3d
    ralbidv
    anbi2d
    bitr4d
end
