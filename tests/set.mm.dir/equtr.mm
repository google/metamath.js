include "weq.mm"
include "wi.mm"
include "ax7.mm"
include "equcoms.mm"

theorem equtr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( y = z -> x = z ) )

  proof
    vy
    vz
    weq
    vx
    vz
    weq
    wi
    vy
    vx
    vy
    vx
    vz
    ax7
    equcoms
end
