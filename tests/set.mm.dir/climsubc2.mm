include "cz.mm"
include "csn.mm"
include "cxp.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cli.mm"
include "wbr.mm"
include "0z.mm"
include "uzssz.mm"
include "zex.mm"
include "climconst2.mm"
include "sylancl.mm"
include "cv.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cuz.mm"
include "eluzelz.mm"
include "eleq2s.mm"
include "fvconst2g.mm"
include "syl2an.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "cmin.mm"
include "co.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "climsub.mm"

theorem climsubc2
  let wph: wff ph
  let cA: class A
  let cC: class C
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cW: class W
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vj: setvar j
  let cH: class H
  assume climadd.1: |- Z = ( ZZ>= ` M )
  assume climadd.2: |- ( ph -> M e. ZZ )
  assume climadd.4: |- ( ph -> F ~~> A )
  assume climaddc1.5: |- ( ph -> C e. CC )
  assume climaddc1.6: |- ( ph -> G e. W )
  assume climaddc1.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climsubc2.h: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( C - ( F ` k ) ) )

  disjoint C k
  disjoint F k
  disjoint k ph
  disjoint A k
  disjoint G k
  disjoint M k
  disjoint Z k
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
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
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint M j
  disjoint M x
  disjoint Z j
  disjoint Z x
  disjoint Z y
  disjoint Z z
  assert |- ( ph -> G ~~> ( C - A ) )

  proof
    wph
    cC
    cA
    vk
    cz
    cC
    csn
    cxp
    #
    cF
    cG
    cM
    cW
    cZ
    climadd.1
    climadd.2
    wph
    cC
    cc
    wcel
    #
    cc0
    cz
    wcel
    @0
    cC
    cli
    wbr
    climaddc1.5
    0z
    cC
    cc0
    cz
    cc0
    uzssz
    zex
    climconst2
    sylancl
    climaddc1.6
    climadd.4
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @2
    @0
    cfv
    #
    cC
    cc
    wph
    @1
    @2
    cz
    wcel
    #
    @5
    cC
    wceq
    @3
    climaddc1.5
    @6
    @2
    cM
    cuz
    cfv
    cZ
    cM
    @2
    eluzelz
    climadd.1
    eleq2s
    cz
    cC
    @2
    cc
    fvconst2g
    syl2an
    #
    wph
    @1
    @3
    climaddc1.5
    adantr
    eqeltrd
    climaddc1.7
    @4
    @2
    cG
    cfv
    cC
    @2
    cF
    cfv
    #
    cmin
    co
    @5
    @8
    cmin
    co
    climsubc2.h
    @4
    @5
    cC
    @8
    cmin
    @7
    oveq1d
    eqtr4d
    climsub
end
