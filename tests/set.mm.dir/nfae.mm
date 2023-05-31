include "weq.mm"
include "wal.mm"
include "hbae.mm"
include "nf5i.mm"

theorem nfae
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- F/ z A. x x = y

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vx
    vy
    vz
    hbae
    nf5i
end
