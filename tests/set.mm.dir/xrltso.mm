include "cxr.mm"
include "clt.mm"
include "cv.mm"
include "xrlttri.mm"
include "xrlttr.mm"
include "isso2i.mm"

theorem xrltso
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- < Or RR*

  proof
    vx
    vy
    vz
    cxr
    clt
    vx
    cv
    #
    vy
    cv
    #
    xrlttri
    @0
    @1
    vz
    cv
    xrlttr
    isso2i
end
