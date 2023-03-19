include "cima.mm"
include "cres.mm"
include "crn.mm"
include "cv.mm"
include "wbr.mm"
include "wex.mm"
include "cab.mm"
include "wrex.mm"
include "df-ima.mm"
include "dfrn2.mm"
include "wcel.mm"
include "wa.mm"
include "vex.mm"
include "brres.mm"
include "ancom.mm"
include "bitri.mm"
include "exbii.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "abbii.mm"
include "3eqtri.mm"

theorem dfima2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( A " B ) = { y | E. x e. B x A y }

  proof
    cA
    cB
    cima
    cA
    cB
    cres
    #
    crn
    vx
    cv
    #
    vy
    cv
    #
    @0
    wbr
    #
    vx
    wex
    #
    vy
    cab
    @1
    @2
    cA
    wbr
    #
    vx
    cB
    wrex
    #
    vy
    cab
    cA
    cB
    df-ima
    vx
    vy
    @0
    dfrn2
    @4
    @6
    vy
    @4
    @1
    cB
    wcel
    #
    @5
    wa
    #
    vx
    wex
    @6
    @3
    @8
    vx
    @3
    @5
    @7
    wa
    @8
    @1
    @2
    cA
    cB
    vy
    vex
    brres
    @5
    @7
    ancom
    bitri
    exbii
    @5
    vx
    cB
    df-rex
    bitr4i
    abbii
    3eqtri
end
