include "cv.mm"
include "wss.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "ax-pow.mm"
include "dfss2.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axpow2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint w x
  disjoint w y
  disjoint w z
  assert |- E. y A. z ( z C_ x -> z e. y )

  proof
    vz
    cv
    #
    vx
    cv
    #
    wss
    #
    vz
    vy
    wel
    #
    wi
    #
    vz
    wal
    #
    vy
    wex
    vw
    vz
    wel
    vw
    vx
    wel
    wi
    vw
    wal
    #
    @3
    wi
    #
    vz
    wal
    #
    vy
    wex
    vx
    vy
    vz
    vw
    ax-pow
    @5
    @8
    vy
    @4
    @7
    vz
    @2
    @6
    @3
    vw
    @0
    @1
    dfss2
    imbi1i
    albii
    exbii
    mpbir
end
