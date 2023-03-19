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
include "clim2f2.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rexralbidv.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem climd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume climd.1: |- F/ k ph
  assume climd.2: |- F/_ k F
  assume climd.3: |- Z = ( ZZ>= ` M )
  assume climd.4: |- ( ph -> M e. ZZ )
  assume climd.5: |- ( ph -> F ~~> A )
  assume climd.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume climd.7: |- ( ph -> X e. RR+ )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint M j
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint A x
  disjoint j x
  disjoint k x
  disjoint B x
  disjoint F x
  disjoint X x
  disjoint Z x
  disjoint ph x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` ( B - A ) ) < X ) )

  proof
    wph
    cX
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
    cX
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
    climd.7
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
    climd.5
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
    climd.1
    climd.2
    climd.3
    climd.4
    wph
    @12
    cF
    cvv
    wcel
    climd.5
    cF
    cA
    cli
    climrel
    brrelexi
    syl
    climd.6
    clim2f2
    mpbid
    simprd
    @6
    @10
    vx
    cX
    crp
    @2
    cX
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
    cX
    @1
    clt
    breq2
    anbi2d
    rexralbidv
    rspcva
    syl2anc
end
