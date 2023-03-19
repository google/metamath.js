include "cixp.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cvv.mm"
include "wfn.mm"
include "wral.mm"
include "elixp2.mm"
include "simp3bi.mm"
include "r19.21bi.mm"

theorem fvixp2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint A x
  disjoint F x
  assert |- ( ( F e. X_ x e. A B /\ x e. A ) -> ( F ` x ) e. B )

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
    cF
    cfv
    cB
    wcel
    #
    vx
    cA
    @0
    cF
    cvv
    wcel
    cF
    cA
    wfn
    @1
    vx
    cA
    wral
    vx
    cA
    cB
    cF
    elixp2
    simp3bi
    r19.21bi
end
