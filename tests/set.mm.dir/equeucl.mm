include "weq.mm"
include "equeuclr.mm"
include "com12.mm"

theorem equeucl
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( x = z -> ( y = z -> x = y ) )

  proof
    vy
    vz
    weq
    vx
    vz
    weq
    vx
    vy
    weq
    vy
    vx
    vz
    equeuclr
    com12
end
