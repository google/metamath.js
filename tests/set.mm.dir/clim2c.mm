include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "cli.mm"
include "biantrurd.mm"
include "wb.mm"
include "uztrn2.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "clim2.mm"
include "3bitr4rd.mm"

theorem clim2c
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
  assume clim2.1: |- Z = ( ZZ>= ` M )
  assume clim2.2: |- ( ph -> M e. ZZ )
  assume clim2.3: |- ( ph -> F e. V )
  assume clim2.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume clim2c.5: |- ( ph -> A e. CC )
  assume clim2c.6: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  assert |- ( ph -> ( F ~~> A <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( B - A ) ) < x ) )

  proof
    wph
    cB
    cc
    wcel
    #
    cB
    cA
    cmin
    co
    cabs
    cfv
    vx
    cv
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
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    cA
    cc
    wcel
    #
    @7
    wa
    @1
    vk
    @4
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    cF
    cA
    cli
    wbr
    wph
    @8
    @7
    clim2c.5
    biantrurd
    wph
    @10
    @6
    vx
    crp
    wph
    @9
    @5
    vj
    cZ
    wph
    @3
    cZ
    wcel
    #
    wa
    @1
    @2
    vk
    @4
    wph
    @11
    vk
    cv
    #
    @4
    wcel
    #
    @1
    @2
    wb
    #
    @11
    @13
    wa
    wph
    @12
    cZ
    wcel
    #
    @14
    cM
    @12
    @3
    cZ
    clim2.1
    uztrn2
    wph
    @15
    wa
    @0
    @1
    clim2c.6
    biantrurd
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    wph
    vx
    cA
    cB
    vj
    vk
    cF
    cM
    cV
    cZ
    clim2.1
    clim2.2
    clim2.3
    clim2.4
    clim2
    3bitr4rd
end
