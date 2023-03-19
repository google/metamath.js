include "cv.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "df-clel.mm"
include "3bitr4g.mm"

theorem eleq2w
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z


  assert |- ( x = y -> ( A e. x <-> A e. y ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vz
    cv
    #
    cA
    wceq
    #
    @3
    @0
    wcel
    #
    wa
    #
    vz
    wex
    @4
    @3
    @1
    wcel
    #
    wa
    #
    vz
    wex
    cA
    @0
    wcel
    cA
    @1
    wcel
    @2
    @6
    @8
    vz
    @2
    @5
    @7
    @4
    vx
    vy
    vz
    elequ2
    anbi2d
    exbidv
    vz
    cA
    @0
    df-clel
    vz
    cA
    @1
    df-clel
    3bitr4g
end
