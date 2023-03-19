include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "eleq2.mm"
include "biimpd.mm"
include "ralrimiv.mm"

theorem raleleq
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A = B -> A. x e. A x e. B )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cB
    wcel
    #
    vx
    cA
    @0
    @1
    cA
    wcel
    @2
    cA
    cB
    @1
    eleq2
    biimpd
    ralrimiv
end
