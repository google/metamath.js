include "weq.mm"
include "wsb.mm"
include "frege55lem2b.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "df-sb.mm"
include "cv.mm"
include "eqtr2.mm"
include "exlimiv.mm"
include "adantl.mm"
include "sylbi.mm"
include "syl.mm"

theorem frege55b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> y = x )

  proof
    vx
    vy
    weq
    vz
    vx
    weq
    #
    vz
    vy
    wsb
    #
    vy
    vx
    weq
    #
    vx
    vy
    vz
    frege55lem2b
    @1
    vz
    vy
    weq
    #
    @0
    wi
    #
    @3
    @0
    wa
    #
    vz
    wex
    #
    wa
    @2
    @0
    vz
    vy
    df-sb
    @6
    @2
    @4
    @5
    @2
    vz
    vz
    cv
    vy
    cv
    vx
    cv
    eqtr2
    exlimiv
    adantl
    sylbi
    syl
end
