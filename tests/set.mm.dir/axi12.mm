include "weq.mm"
include "wal.mm"
include "wo.mm"
include "wi.mm"
include "nfae.mm"
include "nfor.mm"
include "19.32.mm"
include "wn.mm"
include "axc9.mm"
include "orrd.mm"
include "orri.mm"
include "orass.mm"
include "mpbir.mm"
include "mpgbi.mm"
include "mpbi.mm"

theorem axi12
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. z z = x \/ ( A. z z = y \/ A. z ( x = y -> A. z x = y ) ) )

  proof
    vz
    vx
    weq
    vz
    wal
    #
    vz
    vy
    weq
    vz
    wal
    #
    wo
    #
    vx
    vy
    weq
    #
    @3
    vz
    wal
    wi
    #
    vz
    wal
    #
    wo
    #
    @0
    @1
    @5
    wo
    wo
    @2
    @4
    wo
    #
    @6
    vz
    @2
    @4
    vz
    @0
    @1
    vz
    vz
    vx
    vz
    nfae
    vz
    vy
    vz
    nfae
    nfor
    19.32
    @7
    @0
    @1
    @4
    wo
    #
    wo
    @0
    @8
    @0
    wn
    @1
    @4
    vx
    vy
    vz
    axc9
    orrd
    orri
    @0
    @1
    @4
    orass
    mpbir
    mpgbi
    @0
    @1
    @5
    orass
    mpbi
end
