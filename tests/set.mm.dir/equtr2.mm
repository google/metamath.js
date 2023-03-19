include "weq.mm"
include "equeucl.mm"
include "imp.mm"

theorem equtr2
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( ( x = z /\ y = z ) -> x = y )

  proof
    vx
    vz
    weq
    vy
    vz
    weq
    vx
    vy
    weq
    vx
    vy
    vz
    equeucl
    imp
end
