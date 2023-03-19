include "weq.mm"
include "cab.mm"
include "cv.mm"
include "cep.mm"
include "wbr.mm"
include "wex.mm"
include "cvv.mm"
include "cdm.mm"
include "equid.mm"
include "wel.mm"
include "el.mm"
include "epel.mm"
include "exbii.mm"
include "mpbir.mm"
include "2th.mm"
include "abbii.mm"
include "df-v.mm"
include "df-dm.mm"
include "3eqtr4ri.mm"

theorem domep
  let vx: setvar x
  let vy: setvar y


  assert |- dom _E = _V

  proof
    vx
    vx
    weq
    #
    vx
    cab
    vx
    cv
    vy
    cv
    cep
    wbr
    #
    vy
    wex
    #
    vx
    cab
    cvv
    cep
    cdm
    @0
    @2
    vx
    @0
    @2
    vx
    equid
    @2
    vx
    vy
    wel
    #
    vy
    wex
    vx
    vy
    el
    @1
    @3
    vy
    vx
    vy
    epel
    exbii
    mpbir
    2th
    abbii
    vx
    df-v
    vx
    vy
    cep
    df-dm
    3eqtr4ri
end
