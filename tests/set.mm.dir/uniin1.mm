include "cv.mm"
include "cin.mm"
include "ciun.mm"
include "cuni.mm"
include "iunin1.mm"
include "uniiun.mm"
include "ineq1i.mm"
include "eqtr4i.mm"

theorem uniin1
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- U_ x e. A ( x i^i B ) = ( U. A i^i B )

  proof
    vx
    cA
    vx
    cv
    #
    cB
    cin
    ciun
    vx
    cA
    @0
    ciun
    #
    cB
    cin
    cA
    cuni
    #
    cB
    cin
    vx
    cA
    cB
    @0
    iunin1
    @2
    @1
    cB
    vx
    cA
    uniiun
    ineq1i
    eqtr4i
end
