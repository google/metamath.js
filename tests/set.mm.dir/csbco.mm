include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "abeq2i.mm"
include "sbcbii.mm"
include "sbcco.mm"
include "bitri.mm"
include "abbii.mm"
include "3eqtr4i.mm"

theorem csbco
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z

  disjoint B y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint x z
  assert |- [_ A / y ]_ [_ y / x ]_ B = [_ A / x ]_ B

  proof
    vz
    cv
    #
    vx
    vy
    cv
    #
    cB
    csb
    #
    wcel
    #
    vy
    cA
    wsbc
    #
    vz
    cab
    @0
    cB
    wcel
    #
    vx
    cA
    wsbc
    #
    vz
    cab
    vy
    cA
    @2
    csb
    vx
    cA
    cB
    csb
    @4
    @6
    vz
    @4
    @5
    vx
    @1
    wsbc
    #
    vy
    cA
    wsbc
    @6
    @3
    @7
    vy
    cA
    @7
    vz
    @2
    vx
    vz
    @1
    cB
    df-csb
    abeq2i
    sbcbii
    @5
    vx
    vy
    cA
    sbcco
    bitri
    abbii
    vy
    vz
    cA
    @2
    df-csb
    vx
    vz
    cA
    cB
    df-csb
    3eqtr4i
end
