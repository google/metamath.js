include "cv.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "rspc2ev.mm"

theorem rspceov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cF: class F

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  assert |- ( ( C e. A /\ D e. B /\ S = ( C F D ) ) -> E. x e. A E. y e. B S = ( x F y ) )

  proof
    cS
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    wceq
    cS
    cC
    cD
    cF
    co
    #
    wceq
    cS
    cC
    @1
    cF
    co
    #
    wceq
    vx
    vy
    cC
    cD
    cA
    cB
    @0
    cC
    wceq
    @2
    @4
    cS
    @0
    cC
    @1
    cF
    oveq1
    eqeq2d
    @1
    cD
    wceq
    @4
    @3
    cS
    @1
    cD
    cC
    cF
    oveq2
    eqeq2d
    rspc2ev
end
