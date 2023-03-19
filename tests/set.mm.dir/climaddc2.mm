include "caddc.mm"
include "co.mm"
include "cli.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc.mm"
include "adantr.mm"
include "addcomd.mm"
include "eqtrd.mm"
include "climaddc1.mm"
include "wbr.mm"
include "climcl.mm"
include "syl.mm"
include "breqtrd.mm"

theorem climaddc2
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
  assume climaddc2.h: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( C + ( F ` k ) ) )

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
  assert |- ( ph -> G ~~> ( C + A ) )

  proof
    wph
    cG
    cA
    cC
    caddc
    co
    cC
    cA
    caddc
    co
    cli
    wph
    cA
    cC
    vk
    cF
    cG
    cM
    cW
    cZ
    climadd.1
    climadd.2
    climadd.4
    climaddc1.5
    climaddc1.6
    climaddc1.7
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    @0
    cG
    cfv
    cC
    @0
    cF
    cfv
    #
    caddc
    co
    @3
    cC
    caddc
    co
    climaddc2.h
    @2
    cC
    @3
    wph
    cC
    cc
    wcel
    @1
    climaddc1.5
    adantr
    climaddc1.7
    addcomd
    eqtrd
    climaddc1
    wph
    cA
    cC
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    climadd.4
    cA
    cF
    climcl
    syl
    climaddc1.5
    addcomd
    breqtrd
end
