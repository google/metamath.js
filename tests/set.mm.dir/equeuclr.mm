include "weq.mm"
include "wi.mm"
include "equtrr.mm"
include "equcoms.mm"

theorem equeuclr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = z -> ( y = z -> y = x ) )

  proof
    vy
    vz
    weq
    vy
    vx
    weq
    wi
    vz
    vx
    vz
    vx
    vy
    equtrr
    equcoms
end
