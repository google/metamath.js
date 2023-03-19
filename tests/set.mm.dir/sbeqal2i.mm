include "cv.mm"
include "sbeqal1i.mm"
include "eqcomi.mm"

theorem sbeqal2i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sbeqal1i.1: |- ( x = y -> x = z )

  disjoint x z
  assert |- z = y

  proof
    vy
    cv
    vz
    cv
    vx
    vy
    vz
    sbeqal1i.1
    sbeqal1i
    eqcomi
end
