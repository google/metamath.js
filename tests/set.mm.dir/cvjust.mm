include "cv.mm"
include "wcel.mm"
include "cab.mm"
include "wceq.mm"
include "wb.mm"
include "dfcleq.mm"
include "wsb.mm"
include "df-clab.mm"
include "elsb3.mm"
include "bitr2i.mm"
include "mpgbir.mm"

theorem cvjust
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- x = { y | y e. x }

  proof
    vx
    cv
    #
    vy
    cv
    @0
    wcel
    #
    vy
    cab
    #
    wceq
    vz
    cv
    #
    @0
    wcel
    #
    @3
    @2
    wcel
    #
    wb
    vz
    vz
    @0
    @2
    dfcleq
    @5
    @1
    vy
    vz
    wsb
    @4
    @1
    vz
    vy
    df-clab
    vz
    vy
    vx
    elsb3
    bitr2i
    mpgbir
end
