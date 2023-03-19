include "wfun.mm"
include "cxp.mm"
include "cdm.mm"
include "wss.mm"
include "wa.mm"
include "cima.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "co.mm"
include "funimass4.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "eleq1d.mm"
include "ralxp.mm"
include "syl6bb.mm"

theorem funimassov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vz: setvar z
  let cD: class D

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint F z
  assert |- ( ( Fun F /\ ( A X. B ) C_ dom F ) -> ( ( F " ( A X. B ) ) C_ C <-> A. x e. A A. y e. B ( x F y ) e. C ) )

  proof
    cF
    wfun
    cA
    cB
    cxp
    #
    cF
    cdm
    wss
    wa
    cF
    @0
    cima
    cC
    wss
    vz
    cv
    #
    cF
    cfv
    #
    cC
    wcel
    #
    vz
    @0
    wral
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cC
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    vz
    @0
    cC
    cF
    funimass4
    @3
    @7
    vz
    vx
    vy
    cA
    cB
    @1
    @4
    @5
    cop
    #
    wceq
    #
    @2
    @6
    cC
    @9
    @2
    @8
    cF
    cfv
    @6
    @1
    @8
    cF
    fveq2
    @4
    @5
    cF
    df-ov
    syl6eqr
    eleq1d
    ralxp
    syl6bb
end
