include "weq.mm"
include "ax7.mm"
include "equtr.mm"
include "impbid.mm"

theorem equequ1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( x = z <-> y = z ) )

  proof
    vx
    vy
    weq
    vx
    vz
    weq
    vy
    vz
    weq
    vx
    vy
    vz
    ax7
    vx
    vy
    vz
    equtr
    impbid
end
