include "weq.mm"
include "equid.mm"
include "ax7v2.mm"
include "mpi.mm"

theorem equcomiv
  let vx: setvar x
  let vy: setvar y

  disjoint x y
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
    ax7v2
    mpi
end
