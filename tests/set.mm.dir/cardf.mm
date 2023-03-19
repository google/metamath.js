include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "ccrd.mm"
include "wf.mm"
include "cvv.mm"
include "cardf2.mm"
include "cdm.mm"
include "fdmi.mm"
include "cardeqv.mm"
include "eqtr3i.mm"
include "feq2i.mm"
include "mpbi.mm"

theorem cardf
  let vx: setvar x
  let vy: setvar y


  assert |- card : _V --> On

  proof
    vy
    cv
    vx
    cv
    cen
    wbr
    vy
    con0
    wrex
    vx
    cab
    #
    con0
    ccrd
    wf
    cvv
    con0
    ccrd
    wf
    vx
    vy
    cardf2
    #
    @0
    cvv
    con0
    ccrd
    ccrd
    cdm
    @0
    cvv
    @0
    con0
    ccrd
    @1
    fdmi
    cardeqv
    eqtr3i
    feq2i
    mpbi
end
