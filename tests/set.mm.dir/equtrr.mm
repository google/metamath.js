include "weq.mm"
include "equtr.mm"
include "com12.mm"

theorem equtrr
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( x = y -> ( z = x -> z = y ) )

  proof
    vz
    vx
    weq
    vx
    vy
    weq
    vz
    vy
    weq
    vz
    vx
    vy
    equtr
    com12
end
