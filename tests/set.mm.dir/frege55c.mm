include "cv.mm"
include "wceq.mm"
include "weq.mm"
include "wsbc.mm"
include "wi.mm"
include "cvv.mm"
include "vex.mm"
include "frege54cor1c.mm"
include "frege53c.mm"
include "ax-mp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "wcel.mm"
include "df-sbc.mm"
include "clelab.mm"
include "bitri.mm"
include "eqtr2.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "syl.mm"

theorem frege55c
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- ( x = A -> A = x )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    vy
    vx
    weq
    #
    vy
    cA
    wsbc
    #
    cA
    @0
    wceq
    #
    @2
    vy
    @0
    wsbc
    @1
    @3
    wi
    vy
    @0
    cvv
    vx
    vex
    frege54cor1c
    @2
    vy
    @0
    cA
    frege53c
    ax-mp
    @3
    vy
    cv
    #
    cA
    wceq
    @2
    wa
    #
    vy
    wex
    #
    @4
    @3
    cA
    @2
    vy
    cab
    wcel
    @7
    @2
    vy
    cA
    df-sbc
    @2
    vy
    cA
    clelab
    bitri
    @6
    @4
    vy
    @5
    cA
    @0
    eqtr2
    exlimiv
    sylbi
    syl
end
