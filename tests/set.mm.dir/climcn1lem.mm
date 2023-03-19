include "cc.mm"
include "cli.mm"
include "wbr.mm"
include "wcel.mm"
include "climcl.mm"
include "syl.mm"
include "cv.mm"
include "cfv.mm"
include "ffvelrni.mm"
include "adantl.mm"
include "crp.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "sylan.mm"
include "climcn1.mm"

theorem climcn1lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cW: class W
  let cZ: class Z
  assume climcn1lem.1: |- Z = ( ZZ>= ` M )
  assume climcn1lem.2: |- ( ph -> F ~~> A )
  assume climcn1lem.4: |- ( ph -> G e. W )
  assume climcn1lem.5: |- ( ph -> M e. ZZ )
  assume climcn1lem.6: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume climcn1lem.7: |- H : CC --> CC
  assume climcn1lem.8: |- ( ( A e. CC /\ x e. RR+ ) -> E. y e. RR+ A. z e. CC ( ( abs ` ( z - A ) ) < y -> ( abs ` ( ( H ` z ) - ( H ` A ) ) ) < x ) )
  assume climcn1lem.9: |- ( ( ph /\ k e. Z ) -> ( G ` k ) = ( H ` ( F ` k ) ) )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint G k
  disjoint G x
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint Z k
  disjoint Z y
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint M k
  assert |- ( ph -> G ~~> ( H ` A ) )

  proof
    wph
    vx
    vy
    vz
    cA
    cc
    vk
    cH
    cF
    cG
    cM
    cW
    cZ
    climcn1lem.1
    climcn1lem.5
    wph
    cF
    cA
    cli
    wbr
    cA
    cc
    wcel
    #
    climcn1lem.2
    cA
    cF
    climcl
    syl
    #
    vz
    cv
    #
    cc
    wcel
    @2
    cH
    cfv
    #
    cc
    wcel
    wph
    cc
    cc
    @2
    cH
    climcn1lem.7
    ffvelrni
    adantl
    climcn1lem.2
    climcn1lem.4
    wph
    @0
    vx
    cv
    #
    crp
    wcel
    @2
    cA
    cmin
    co
    cabs
    cfv
    vy
    cv
    clt
    wbr
    @3
    cA
    cH
    cfv
    cmin
    co
    cabs
    cfv
    @4
    clt
    wbr
    wi
    vz
    cc
    wral
    vy
    crp
    wrex
    @1
    climcn1lem.8
    sylan
    climcn1lem.6
    climcn1lem.9
    climcn1
end
