include "cuni.mm"
include "wel.mm"
include "wrex.mm"
include "cab.mm"
include "cv.mm"
include "ciun.mm"
include "dfuni2.mm"
include "df-iun.mm"
include "eqtr4i.mm"

theorem uniiun
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- U. A = U_ x e. A x

  proof
    cA
    cuni
    vy
    vx
    wel
    vx
    cA
    wrex
    vy
    cab
    vx
    cA
    vx
    cv
    #
    ciun
    vy
    vx
    cA
    dfuni2
    vx
    vy
    cA
    @0
    df-iun
    eqtr4i
end
