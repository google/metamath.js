include "weq.mm"
include "wi.mm"
include "wal.mm"
include "equtrr.mm"
include "alrimiv.mm"
include "sbeqal1.mm"
include "impbii.mm"

theorem sbeqalbi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint y z
  disjoint x z
  assert |- ( x = y <-> A. z ( z = x -> z = y ) )

  proof
    vx
    vy
    weq
    #
    vz
    vx
    weq
    vz
    vy
    weq
    wi
    #
    vz
    wal
    @0
    @1
    vz
    vx
    vy
    vz
    equtrr
    alrimiv
    vz
    vx
    vy
    sbeqal1
    impbii
end
