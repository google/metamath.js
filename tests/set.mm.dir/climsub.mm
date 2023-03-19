include "cc.mm"
include "cmin.mm"
include "cli.mm"
include "wbr.mm"
include "wcel.mm"
include "climcl.mm"
include "syl.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "subcl.mm"
include "adantl.mm"
include "crp.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "simpr.mm"
include "adantr.mm"
include "subcn2.mm"
include "syl3anc.mm"
include "climcn2.mm"

theorem climsub
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let vj: setvar j
  assume climadd.1: |- Z = ( ZZ>= ` M )
  assume climadd.2: |- ( ph -> M e. ZZ )
  assume climadd.4: |- ( ph -> F ~~> A )
  assume climadd.6: |- ( ph -> H e. X )
  assume climadd.7: |- ( ph -> G ~~> B )
  assume climadd.8: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climadd.9: |- ( ( ph /\ k e. Z ) -> ( G ` k ) e. CC )
  assume climsub.h: |- ( ( ph /\ k e. Z ) -> ( H ` k ) = ( ( F ` k ) - ( G ` k ) ) )

  disjoint B k
  disjoint F k
  disjoint k ph
  disjoint A k
  disjoint G k
  disjoint H k
  disjoint M k
  disjoint Z k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C k
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  disjoint j x
  disjoint j ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint A j
  disjoint A u
  disjoint A v
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint G j
  disjoint G v
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint M j
  disjoint M x
  disjoint Z j
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> H ~~> ( A - B ) )

  proof
    wph
    vx
    vy
    vz
    vv
    vu
    cA
    cB
    cc
    cc
    vk
    cmin
    cF
    cG
    cH
    cM
    cX
    cZ
    climadd.1
    climadd.2
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    #
    climadd.4
    cA
    cF
    climcl
    syl
    #
    wph
    cG
    cB
    cli
    wbr
    cB
    cc
    wcel
    #
    climadd.7
    cB
    cG
    climcl
    syl
    #
    vu
    cv
    #
    cc
    wcel
    vv
    cv
    #
    cc
    wcel
    wa
    @4
    @5
    cmin
    co
    #
    cc
    wcel
    wph
    @4
    @5
    subcl
    adantl
    climadd.4
    climadd.7
    climadd.6
    wph
    vx
    cv
    #
    crp
    wcel
    #
    wa
    @8
    @0
    @2
    @4
    cA
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    @5
    cB
    cmin
    co
    cabs
    cfv
    vz
    cv
    clt
    wbr
    wa
    @6
    cA
    cB
    cmin
    co
    cmin
    co
    cabs
    cfv
    @7
    clt
    wbr
    wi
    vv
    cc
    wral
    vu
    cc
    wral
    vz
    crp
    wrex
    vy
    crp
    wrex
    wph
    @8
    simpr
    wph
    @0
    @8
    @1
    adantr
    wph
    @2
    @8
    @3
    adantr
    vy
    vz
    vv
    vu
    @7
    cA
    cB
    subcn2
    syl3anc
    climadd.8
    climadd.9
    climsub.h
    climcn2
end
