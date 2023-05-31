include "weq.mm"
include "equid.mm"
include "ax7.mm"
include "mpi.mm"

theorem equcomi
  param vx: setvar x
  param vy: setvar y


  assert |- ( x = y -> y = x )

  proof
    vx
    vy
    weq
    vx
    vx
    weq
    vy
    vx
    weq
    vx
    equid
    vx
    vy
    vx
    ax7
    mpi
end
