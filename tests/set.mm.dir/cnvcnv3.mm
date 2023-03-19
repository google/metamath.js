include "ccnv.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "df-cnv.mm"
include "vex.mm"
include "brcnv.mm"
include "opabbii.mm"
include "eqtri.mm"

theorem cnvcnv3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint x y
  disjoint R x
  disjoint R y
  assert |- `' `' R = { <. x , y >. | x R y }

  proof
    cR
    ccnv
    #
    ccnv
    vy
    cv
    #
    vx
    cv
    #
    @0
    wbr
    #
    vx
    vy
    copab
    @2
    @1
    cR
    wbr
    #
    vx
    vy
    copab
    vx
    vy
    @0
    df-cnv
    @3
    @4
    vx
    vy
    @1
    @2
    cR
    vy
    vex
    vx
    vex
    brcnv
    opabbii
    eqtri
end
