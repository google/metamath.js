include "wel.mm"
include "wal.mm"
include "wn.mm"
include "nd3.mm"
include "aecoms.mm"

theorem nd4
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> -. A. z y e. x )

  proof
    vy
    vx
    wel
    vz
    wal
    wn
    vy
    vx
    vy
    vx
    vz
    nd3
    aecoms
end
