include "cv.mm"
include "cin.mm"
include "ciun.mm"
include "cuni.mm"
include "iunin2.mm"
include "uniiun.mm"
include "ineq2i.mm"
include "eqtr4i.mm"

theorem uniin2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- U_ x e. B ( A i^i x ) = ( A i^i U. B )

  proof
    vx
    cB
    cA
    vx
    cv
    #
    cin
    ciun
    cA
    vx
    cB
    @0
    ciun
    #
    cin
    cA
    cB
    cuni
    #
    cin
    vx
    cB
    cA
    @0
    iunin2
    @2
    @1
    cA
    vx
    cB
    uniiun
    ineq2i
    eqtr4i
end
