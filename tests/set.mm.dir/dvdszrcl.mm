include "cz.mm"
include "cdvds.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "df-dvds.mm"
include "opabssxp.mm"
include "eqsstri.mm"
include "brel.mm"

theorem dvdszrcl
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( X || Y -> ( X e. ZZ /\ Y e. ZZ ) )

  proof
    cX
    cY
    cz
    cz
    cdvds
    cdvds
    vx
    cv
    #
    cz
    wcel
    vy
    cv
    #
    cz
    wcel
    wa
    vz
    cv
    @0
    cmul
    co
    @1
    wceq
    vz
    cz
    wrex
    #
    wa
    vx
    vy
    copab
    cz
    cz
    cxp
    vx
    vy
    vz
    df-dvds
    @2
    vx
    vy
    cz
    cz
    opabssxp
    eqsstri
    brel
end
