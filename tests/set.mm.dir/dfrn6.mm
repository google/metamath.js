include "crn.mm"
include "ccnv.mm"
include "cdm.mm"
include "cv.mm"
include "cec.mm"
include "c0.mm"
include "wne.mm"
include "cab.mm"
include "df-rn.mm"
include "dfdm6.mm"
include "eqtri.mm"

theorem dfrn6
  let vx: setvar x
  let cR: class R

  disjoint R x
  assert |- ran R = { x | [ x ] `' R =/= (/) }

  proof
    cR
    crn
    cR
    ccnv
    #
    cdm
    vx
    cv
    @0
    cec
    c0
    wne
    vx
    cab
    cR
    df-rn
    vx
    @0
    dfdm6
    eqtri
end
