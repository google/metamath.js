include "cixp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "cvv.mm"
include "wfn.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem fvixp
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let vf: setvar f
  assume fvixp.1: |- ( x = C -> B = D )

  disjoint A x
  disjoint C x
  disjoint D x
  disjoint F x
  disjoint f x
  disjoint A f
  disjoint B f
  disjoint F f
  assert |- ( ( F e. X_ x e. A B /\ C e. A ) -> ( F ` C ) e. D )

  proof
    cF
    vx
    cA
    cB
    cixp
    wcel
    #
    vx
    cv
    #
    cF
    cfv
    #
    cB
    wcel
    #
    vx
    cA
    wral
    #
    cC
    cA
    wcel
    cC
    cF
    cfv
    #
    cD
    wcel
    #
    @0
    cF
    cvv
    wcel
    cF
    cA
    wfn
    @4
    vx
    cA
    cB
    cF
    elixp2
    simp3bi
    @3
    @6
    vx
    cC
    cA
    @1
    cC
    wceq
    @2
    @5
    cB
    cD
    @1
    cC
    cF
    fveq2
    fvixp.1
    eleq12d
    rspccva
    sylan
end
