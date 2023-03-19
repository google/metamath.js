include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "0cnd.mm"
include "clim2c.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "uztrn2.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem clim0c
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume clim0.1: |- Z = ( ZZ>= ` M )
  assume clim0.2: |- ( ph -> M e. ZZ )
  assume clim0.3: |- ( ph -> F e. V )
  assume clim0.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume clim0c.6: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  assert |- ( ph -> ( F ~~> 0 <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` B ) < x ) )

  proof
    wph
    cF
    cc0
    cli
    wbr
    cB
    cc0
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
    cB
    cabs
    cfv
    #
    @2
    clt
    wbr
    #
    vk
    @5
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    wph
    vx
    cc0
    cB
    vj
    vk
    cF
    cM
    cV
    cZ
    clim0.1
    clim0.2
    clim0.3
    clim0.4
    wph
    0cnd
    clim0c.6
    clim2c
    wph
    @7
    @11
    vx
    crp
    wph
    @6
    @10
    vj
    cZ
    wph
    @4
    cZ
    wcel
    #
    wa
    @3
    @9
    vk
    @5
    wph
    @12
    vk
    cv
    #
    @5
    wcel
    #
    @3
    @9
    wb
    #
    @12
    @14
    wa
    wph
    @13
    cZ
    wcel
    #
    @15
    cM
    @13
    @4
    cZ
    clim0.1
    uztrn2
    wph
    @16
    wa
    #
    @1
    @8
    @2
    clt
    @17
    @0
    cB
    cabs
    @17
    cB
    clim0c.6
    subid1d
    fveq2d
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    bitrd
end
