include "weq.mm"
include "equtrr.mm"
include "equeuclr.mm"
include "impbid.mm"

theorem equequ2
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( x = y -> ( z = x <-> z = y ) )

  proof
    vx
    vy
    weq
    vz
    vx
    weq
    vz
    vy
    weq
    vx
    vy
    vz
    equtrr
    vx
    vz
    vy
    equeuclr
    impbid
end
