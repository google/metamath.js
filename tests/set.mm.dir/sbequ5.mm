include "weq.mm"
include "wal.mm"
include "nfae.mm"
include "sbf.mm"

theorem sbequ5
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( [ w / z ] A. x x = y <-> A. x x = y )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vw
    vx
    vy
    vz
    nfae
    sbf
end
