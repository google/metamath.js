include "weq.mm"
include "wal.mm"
include "nfae.mm"
include "nfn.mm"

theorem nfnae
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- F/ z -. A. x x = y

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
    nfae
    nfn
end
