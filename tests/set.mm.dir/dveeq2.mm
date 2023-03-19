include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfeqf2.mm"
include "nf5rd.mm"

theorem dveeq2
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( z = y -> A. x z = y ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vz
    vy
    weq
    vx
    vx
    vy
    vz
    nfeqf2
    nf5rd
end
