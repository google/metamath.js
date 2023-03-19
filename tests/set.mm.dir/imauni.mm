include "cuni.mm"
include "cima.mm"
include "cv.mm"
include "ciun.mm"
include "uniiun.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "eqtri.mm"

theorem imauni
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A " U. B ) = U_ x e. B ( A " x )

  proof
    cA
    cB
    cuni
    #
    cima
    cA
    vx
    cB
    vx
    cv
    #
    ciun
    #
    cima
    vx
    cB
    cA
    @1
    cima
    ciun
    @0
    @2
    cA
    vx
    cB
    uniiun
    imaeq2i
    vx
    cA
    cB
    @1
    imaiun
    eqtri
end
