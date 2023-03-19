include "weq.mm"
include "wi.mm"
include "sbeqal1.mm"
include "mpg.mm"

theorem sbeqal1i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sbeqal1i.1: |- ( x = y -> x = z )

  disjoint x z
  assert |- y = z

  proof
    vx
    vy
    weq
    vx
    vz
    weq
    wi
    vy
    vz
    weq
    vx
    vx
    vy
    vz
    sbeqal1
    sbeqal1i.1
    mpg
end
