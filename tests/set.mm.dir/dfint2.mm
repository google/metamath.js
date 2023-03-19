include "cint.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "cab.mm"
include "wral.mm"
include "df-int.mm"
include "df-ral.mm"
include "abbii.mm"
include "eqtr4i.mm"

theorem dfint2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- |^| A = { x | A. y e. A x e. y }

  proof
    cA
    cint
    vy
    cv
    #
    cA
    wcel
    vx
    cv
    @0
    wcel
    #
    wi
    vy
    wal
    #
    vx
    cab
    @1
    vy
    cA
    wral
    #
    vx
    cab
    vx
    vy
    cA
    df-int
    @3
    @2
    vx
    @1
    vy
    cA
    df-ral
    abbii
    eqtr4i
end
