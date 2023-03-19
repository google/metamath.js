include "cc.mm"
include "wcel.mm"
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
include "simpr.mm"
include "ralimi.mm"
include "reximi.mm"
include "syl.mm"

theorem climi2
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
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( B - A ) ) < C )

  proof
    wph
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
    @1
    vk
    @3
    wral
    #
    vj
    cZ
    wrex
    wph
    cA
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
    climi.5
    climi
    @4
    @5
    vj
    cZ
    @2
    @1
    vk
    @3
    @0
    @1
    simpr
    ralimi
    reximi
    syl
end
