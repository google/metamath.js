include "wrel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "dfrel2.mm"
include "eqcom.mm"
include "cnvcnv3.mm"
include "eqeq2i.mm"
include "3bitri.mm"

theorem dfrel4v
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint x y
  disjoint R x
  disjoint R y
  assert |- ( Rel R <-> R = { <. x , y >. | x R y } )

  proof
    cR
    wrel
    cR
    ccnv
    ccnv
    #
    cR
    wceq
    cR
    @0
    wceq
    cR
    vx
    cv
    vy
    cv
    cR
    wbr
    vx
    vy
    copab
    #
    wceq
    cR
    dfrel2
    @0
    cR
    eqcom
    @0
    @1
    cR
    vx
    vy
    cR
    cnvcnv3
    eqeq2i
    3bitri
end
