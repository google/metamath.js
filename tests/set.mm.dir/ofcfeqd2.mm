include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cofc.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "eqidd.mm"
include "ofcfval.mm"
include "3eqtr4d.mm"

theorem ofcfeqd2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cF: class F
  let cV: class V
  let cW: class W
  assume ofcfeqd2.1: |- ( ( ph /\ x e. A ) -> ( F ` x ) e. B )
  assume ofcfeqd2.2: |- ( ( ph /\ y e. B ) -> ( y R C ) = ( y P C ) )
  assume ofcfeqd2.3: |- ( ph -> F Fn A )
  assume ofcfeqd2.4: |- ( ph -> A e. V )
  assume ofcfeqd2.5: |- ( ph -> C e. W )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint P x
  disjoint P y
  disjoint R x
  disjoint R y
  disjoint ph x
  disjoint ph y
  disjoint B y
  assert |- ( ph -> ( F oFC R C ) = ( F oFC P C ) )

  proof
    wph
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cC
    cR
    co
    #
    cmpt
    vx
    cA
    @1
    cC
    cP
    co
    #
    cmpt
    cF
    cC
    cR
    cofc
    co
    cF
    cC
    cP
    cofc
    co
    wph
    vx
    cA
    @2
    @3
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    cB
    wcel
    vy
    cv
    #
    cC
    cR
    co
    #
    @6
    cC
    cP
    co
    #
    wceq
    #
    vy
    cB
    wral
    #
    @2
    @3
    wceq
    #
    ofcfeqd2.1
    wph
    @10
    @4
    wph
    @9
    vy
    cB
    ofcfeqd2.2
    ralrimiva
    adantr
    @9
    @11
    vy
    @1
    cB
    @6
    @1
    wceq
    @7
    @2
    @8
    @3
    @6
    @1
    cC
    cR
    oveq1
    @6
    @1
    cC
    cP
    oveq1
    eqeq12d
    rspcva
    syl2anc
    mpteq2dva
    wph
    vx
    cA
    @1
    cC
    cR
    cF
    cV
    cW
    ofcfeqd2.3
    ofcfeqd2.4
    ofcfeqd2.5
    @5
    @1
    eqidd
    #
    ofcfval
    wph
    vx
    cA
    @1
    cC
    cP
    cF
    cV
    cW
    ofcfeqd2.3
    ofcfeqd2.4
    ofcfeqd2.5
    @12
    ofcfval
    3eqtr4d
end
