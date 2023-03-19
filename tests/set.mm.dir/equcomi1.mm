include "weq.mm"
include "equid1.mm"
include "ax7.mm"
include "mpi.mm"

theorem equcomi1
  let vx: setvar x
  let vy: setvar y


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
    equid1
    vx
    vy
    vx
    ax7
    mpi
end
