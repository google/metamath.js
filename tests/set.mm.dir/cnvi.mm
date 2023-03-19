include "cv.mm"
include "cid.mm"
include "wbr.mm"
include "copab.mm"
include "weq.mm"
include "ccnv.mm"
include "vex.mm"
include "ideq.mm"
include "equcom.mm"
include "bitri.mm"
include "opabbii.mm"
include "df-cnv.mm"
include "df-id.mm"
include "3eqtr4i.mm"

theorem cnvi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- `' _I = _I

  proof
    vy
    cv
    #
    vx
    cv
    #
    cid
    wbr
    #
    vx
    vy
    copab
    vx
    vy
    weq
    #
    vx
    vy
    copab
    cid
    ccnv
    cid
    @2
    @3
    vx
    vy
    @2
    vy
    vx
    weq
    @3
    @0
    @1
    vx
    vex
    ideq
    vy
    vx
    equcom
    bitri
    opabbii
    vx
    vy
    cid
    df-cnv
    vx
    vy
    df-id
    3eqtr4i
end
