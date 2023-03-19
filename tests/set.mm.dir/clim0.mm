include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "clim2.mm"
include "0cn.mm"
include "biantrur.mm"
include "subid1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "pm5.32i.mm"
include "ralbii.mm"
include "rexbii.mm"
include "bitr3i.mm"
include "syl6bb.mm"

theorem clim0
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
  assert |- ( ph -> ( F ~~> 0 <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` B ) < x ) ) )

  proof
    wph
    cF
    cc0
    cli
    wbr
    cc0
    cc
    wcel
    #
    cB
    cc
    wcel
    #
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
    wa
    #
    vk
    vj
    cv
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
    wa
    #
    @1
    cB
    cabs
    cfv
    #
    @4
    clt
    wbr
    #
    wa
    #
    vk
    @7
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
    clim2
    @11
    @10
    @17
    @0
    @10
    0cn
    biantrur
    @9
    @16
    vx
    crp
    @8
    @15
    vj
    cZ
    @6
    @14
    vk
    @7
    @1
    @5
    @13
    @1
    @3
    @12
    @4
    clt
    @1
    @2
    cB
    cabs
    cB
    subid1
    fveq2d
    breq1d
    pm5.32i
    ralbii
    rexbii
    ralbii
    bitr3i
    syl6bb
end
