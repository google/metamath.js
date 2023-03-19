include "weq.mm"
include "equtr.mm"
include "com12.mm"

theorem equtrr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


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
