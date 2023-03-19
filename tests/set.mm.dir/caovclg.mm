include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "ralrimivva.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem caovclg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume caovclg.1: |- ( ( ph /\ ( x e. C /\ y e. D ) ) -> ( x F y ) e. E )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  assert |- ( ( ph /\ ( A e. C /\ B e. D ) ) -> ( A F B ) e. E )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cE
    wcel
    #
    vy
    cD
    wral
    vx
    cC
    wral
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cA
    cB
    cF
    co
    #
    cE
    wcel
    #
    wph
    @3
    vx
    vy
    cC
    cD
    caovclg.1
    ralrimivva
    @3
    @5
    cA
    @1
    cF
    co
    #
    cE
    wcel
    vx
    vy
    cA
    cB
    cC
    cD
    @0
    cA
    wceq
    @2
    @6
    cE
    @0
    cA
    @1
    cF
    oveq1
    eleq1d
    @1
    cB
    wceq
    @6
    @4
    cE
    @1
    cB
    cA
    cF
    oveq2
    eleq1d
    rspc2v
    mpan9
end
