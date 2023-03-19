include "csb.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "df-csb.mm"
include "sbc5.mm"
include "abbii.mm"
include "eqtri.mm"

theorem csb2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  assert |- [_ A / x ]_ B = { y | E. x ( x = A /\ y e. B ) }

  proof
    vx
    cA
    cB
    csb
    vy
    cv
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    vx
    cv
    cA
    wceq
    @0
    wa
    vx
    wex
    #
    vy
    cab
    vx
    vy
    cA
    cB
    df-csb
    @1
    @2
    vy
    @0
    vx
    cA
    sbc5
    abbii
    eqtri
end
