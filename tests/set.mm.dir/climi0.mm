include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "climi.mm"
include "subid1.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "biimpa.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl.mm"

theorem climi0
  let wph: wff ph
  let cB: class B
  let cC: class C
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  let cA: class A
  assume climi.1: |- Z = ( ZZ>= ` M )
  assume climi.2: |- ( ph -> M e. ZZ )
  assume climi.3: |- ( ph -> C e. RR+ )
  assume climi.4: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume climi0.5: |- ( ph -> F ~~> 0 )

  disjoint j k
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
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint C x
  disjoint F x
  disjoint ph x
  disjoint Z x
  disjoint B x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` B ) < C )

  proof
    wph
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
    cC
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
    cB
    cabs
    cfv
    #
    cC
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
    wph
    cc0
    cB
    cC
    vj
    vk
    cF
    cM
    cZ
    climi.1
    climi.2
    climi.3
    climi.4
    climi0.5
    climi
    @6
    @9
    vj
    cZ
    @4
    @8
    vk
    @5
    @0
    @3
    @8
    @0
    @2
    @7
    cC
    clt
    @0
    @1
    cB
    cabs
    cB
    subid1
    fveq2d
    breq1d
    biimpa
    ralimi
    reximi
    syl
end
