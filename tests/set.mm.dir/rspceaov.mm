include "cv.mm"
include "caov.mm"
include "wceq.mm"
include "eqidd.mm"
include "id.mm"
include "aoveq123d.mm"
include "eqeq2d.mm"
include "rspc2ev.mm"

theorem rspceaov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cF: class F
  let vk: setvar k

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
  disjoint k x
  assert |- ( ( C e. A /\ D e. B /\ S = (( C F D )) ) -> E. x e. A E. y e. B S = (( x F y )) )

  proof
    cS
    vx
    cv
    #
    vy
    cv
    #
    cF
    caov
    #
    wceq
    cS
    cC
    cD
    cF
    caov
    #
    wceq
    cS
    cC
    @1
    cF
    caov
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
    #
    @2
    @4
    cS
    @5
    @0
    cC
    @1
    @1
    cF
    cF
    @5
    cF
    eqidd
    @5
    id
    @5
    @1
    eqidd
    aoveq123d
    eqeq2d
    @1
    cD
    wceq
    #
    @4
    @3
    cS
    @6
    cC
    cC
    @1
    cD
    cF
    cF
    @6
    cF
    eqidd
    @6
    cC
    eqidd
    @6
    id
    aoveq123d
    eqeq2d
    rspc2ev
end
