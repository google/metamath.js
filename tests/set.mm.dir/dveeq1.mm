include "weq.mm"
include "wal.mm"
include "wn.mm"
include "nfeqf1.mm"
include "nf5rd.mm"

theorem dveeq1
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( y = z -> A. x y = z ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    vy
    vz
    weq
    vx
    vx
    vy
    vz
    nfeqf1
    nf5rd
end
