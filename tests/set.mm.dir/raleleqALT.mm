include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "ralel.mm"
include "id.mm"
include "raleqdv.mm"
include "mpbiri.mm"

theorem raleleqALT
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
    cB
    wcel
    #
    vx
    cA
    wral
    @1
    vx
    cB
    wral
    vx
    cB
    ralel
    @0
    @1
    vx
    cA
    cB
    @0
    id
    raleqdv
    mpbiri
end
