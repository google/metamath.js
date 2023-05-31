include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "df-uni.mm"
include "exancom.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "abbii.mm"
include "eqtri.mm"

theorem dfuni2
  param vx: setvar x
  param vy: setvar y
  param cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- U. A = { x | E. y e. A x e. y }

  proof
    cA
    cuni
    vx
    cv
    vy
    cv
    #
    wcel
    #
    @0
    cA
    wcel
    #
    wa
    vy
    wex
    #
    vx
    cab
    @1
    vy
    cA
    wrex
    #
    vx
    cab
    vx
    vy
    cA
    df-uni
    @3
    @4
    vx
    @3
    @2
    @1
    wa
    vy
    wex
    @4
    @1
    @2
    vy
    exancom
    @1
    vy
    cA
    df-rex
    bitr4i
    abbii
    eqtri
end
