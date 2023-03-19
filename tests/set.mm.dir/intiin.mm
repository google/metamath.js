include "cint.mm"
include "wel.mm"
include "wral.mm"
include "cab.mm"
include "cv.mm"
include "ciin.mm"
include "dfint2.mm"
include "df-iin.mm"
include "eqtr4i.mm"

theorem intiin
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- |^| A = |^|_ x e. A x

  proof
    cA
    cint
    vy
    vx
    wel
    vx
    cA
    wral
    vy
    cab
    vx
    cA
    vx
    cv
    #
    ciin
    vy
    vx
    cA
    dfint2
    vx
    vy
    cA
    @0
    df-iin
    eqtr4i
end
