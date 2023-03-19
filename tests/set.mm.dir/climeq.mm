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
include "wrex.mm"
include "crp.mm"
include "clim2.mm"
include "eqidd.mm"
include "bitr4d.mm"

theorem climeq
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  assume climeq.1: |- Z = ( ZZ>= ` M )
  assume climeq.2: |- ( ph -> F e. V )
  assume climeq.3: |- ( ph -> G e. W )
  assume climeq.5: |- ( ph -> M e. ZZ )
  assume climeq.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = ( G ` k ) )

  disjoint A k
  disjoint F k
  disjoint G k
  disjoint k ph
  disjoint Z k
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint ph x
  disjoint ph y
  disjoint Z y
  disjoint M y
  assert |- ( ph -> ( F ~~> A <-> G ~~> A ) )

  proof
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    vk
    cv
    #
    cG
    cfv
    #
    cc
    wcel
    @1
    cA
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    wa
    vk
    vy
    cv
    cuz
    cfv
    wral
    vy
    cZ
    wrex
    vx
    crp
    wral
    wa
    cG
    cA
    cli
    wbr
    wph
    vx
    cA
    @1
    vy
    vk
    cF
    cM
    cV
    cZ
    climeq.1
    climeq.5
    climeq.2
    climeq.6
    clim2
    wph
    vx
    cA
    @1
    vy
    vk
    cG
    cM
    cW
    cZ
    climeq.1
    climeq.5
    climeq.3
    wph
    @0
    cZ
    wcel
    wa
    @1
    eqidd
    clim2
    bitr4d
end
