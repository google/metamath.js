include "weq.mm"
include "copab.mm"
include "cv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cmpt.mm"
include "equcom.mm"
include "vex.mm"
include "biantrur.mm"
include "bitri.mm"
include "opabbii.mm"
include "df-id.mm"
include "df-mpt.mm"
include "3eqtr4i.mm"

theorem dfid4
  let vx: setvar x
  let vy: setvar y


  assert |- _I = ( x e. _V |-> x )

  proof
    vx
    vy
    weq
    #
    vx
    vy
    copab
    vx
    cv
    #
    cvv
    wcel
    #
    vy
    vx
    weq
    #
    wa
    #
    vx
    vy
    copab
    cid
    vx
    cvv
    @1
    cmpt
    @0
    @4
    vx
    vy
    @0
    @3
    @4
    vx
    vy
    equcom
    @2
    @3
    vx
    vex
    biantrur
    bitri
    opabbii
    vx
    vy
    df-id
    vx
    vy
    cvv
    @1
    df-mpt
    3eqtr4i
end
