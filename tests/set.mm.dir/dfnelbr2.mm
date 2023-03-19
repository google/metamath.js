include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "wel.mm"
include "cdif.mm"
include "wn.mm"
include "cxp.mm"
include "cep.mm"
include "cnelbr.mm"
include "difopab.mm"
include "df-xp.mm"
include "df-eprel.mm"
include "difeq12i.mm"
include "df-nelbr.mm"
include "vex.mm"
include "pm3.2i.mm"
include "biantrur.mm"
include "opabbii.mm"
include "eqtri.mm"
include "3eqtr4ri.mm"

theorem dfnelbr2
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k


  assert |- e// = ( ( _V X. _V ) \ _E )

  proof
    vx
    cv
    cvv
    wcel
    #
    vy
    cv
    cvv
    wcel
    #
    wa
    #
    vx
    vy
    copab
    #
    vx
    vy
    wel
    #
    vx
    vy
    copab
    #
    cdif
    @2
    @4
    wn
    #
    wa
    #
    vx
    vy
    copab
    #
    cvv
    cvv
    cxp
    #
    cep
    cdif
    cnelbr
    @2
    @4
    vx
    vy
    difopab
    @9
    @3
    cep
    @5
    vx
    vy
    cvv
    cvv
    df-xp
    vx
    vy
    df-eprel
    difeq12i
    cnelbr
    @6
    vx
    vy
    copab
    @8
    vx
    vy
    df-nelbr
    @6
    @7
    vx
    vy
    @2
    @6
    @0
    @1
    vx
    vex
    vy
    vex
    pm3.2i
    biantrur
    opabbii
    eqtri
    3eqtr4ri
end
