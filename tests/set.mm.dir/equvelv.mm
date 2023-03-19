include "weq.mm"
include "wi.mm"
include "wal.mm"
include "equtrr.mm"
include "alrimiv.mm"
include "wa.mm"
include "wex.mm"
include "equs4v.mm"
include "equvinv.mm"
include "sylibr.mm"
include "impbii.mm"

theorem equvelv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  disjoint y z
  assert |- ( x = y <-> A. z ( z = x -> z = y ) )

  proof
    vx
    vy
    weq
    #
    vz
    vx
    weq
    #
    vz
    vy
    weq
    #
    wi
    #
    vz
    wal
    #
    @0
    @3
    vz
    vx
    vy
    vz
    equtrr
    alrimiv
    @4
    @1
    @2
    wa
    vz
    wex
    @0
    @2
    vz
    vx
    equs4v
    vx
    vy
    vz
    equvinv
    sylibr
    impbii
end
