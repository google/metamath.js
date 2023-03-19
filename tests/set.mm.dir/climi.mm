include "crp.mm"
include "wcel.mm"
include "cc.mm"
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
include "cli.mm"
include "cvv.mm"
include "climrel.mm"
include "brrelexi.mm"
include "syl.mm"
include "clim2.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem climi
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume climi.1: |- Z = ( ZZ>= ` M )
  assume climi.2: |- ( ph -> M e. ZZ )
  assume climi.3: |- ( ph -> C e. RR+ )
  assume climi.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume climi.5: |- ( ph -> F ~~> A )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint C j
  disjoint C k
  disjoint F j
  disjoint F k
  disjoint j ph
  disjoint k ph
  disjoint Z j
  disjoint Z k
  disjoint M j
  disjoint j x
  disjoint k x
  disjoint A x
  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint Z x
  disjoint B x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` ( B - A ) ) < C ) )

  proof
    wph
    cC
    crp
    wcel
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
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @0
    @1
    cC
    clt
    wbr
    #
    wa
    #
    vk
    @5
    wral
    vj
    cZ
    wrex
    #
    climi.3
    wph
    cA
    cc
    wcel
    #
    @7
    wph
    cF
    cA
    cli
    wbr
    #
    @11
    @7
    wa
    climi.5
    wph
    vx
    cA
    cB
    vj
    vk
    cF
    cM
    cvv
    cZ
    climi.1
    climi.2
    wph
    @12
    cF
    cvv
    wcel
    climi.5
    cF
    cA
    cli
    climrel
    brrelexi
    syl
    climi.4
    clim2
    mpbid
    simprd
    @6
    @10
    vx
    cC
    crp
    @2
    cC
    wceq
    #
    @4
    @9
    vj
    vk
    cZ
    @5
    @13
    @3
    @8
    @0
    @2
    cC
    @1
    clt
    breq2
    anbi2d
    rexralbidv
    rspcv
    sylc
end
