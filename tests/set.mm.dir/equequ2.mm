include "weq.mm"
include "equtrr.mm"
include "equeuclr.mm"
include "impbid.mm"

theorem equequ2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


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
