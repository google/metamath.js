include "cv.mm"
include "csb.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "df-csb.mm"
include "sbcid.mm"
include "abbii.mm"
include "abid2.mm"
include "3eqtri.mm"

theorem csbid
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- [_ x / x ]_ A = A

  proof
    vx
    vx
    cv
    #
    cA
    csb
    vy
    cv
    cA
    wcel
    #
    vx
    @0
    wsbc
    #
    vy
    cab
    @1
    vy
    cab
    cA
    vx
    vy
    @0
    cA
    df-csb
    @2
    @1
    vy
    @1
    vx
    sbcid
    abbii
    vy
    cA
    abid2
    3eqtri
end
