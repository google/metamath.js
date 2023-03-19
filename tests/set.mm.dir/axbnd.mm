include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "nfnae.mm"
include "nfan.mm"
include "axc9.mm"
include "imp.mm"
include "alrimi.mm"
include "ex.mm"
include "orrd.mm"
include "orri.mm"

theorem axbnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. z z = x \/ ( A. z z = y \/ A. x A. z ( x = y -> A. z x = y ) ) )

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
    vx
    vy
    weq
    #
    @2
    vz
    wal
    wi
    #
    vz
    wal
    #
    vx
    wal
    #
    wo
    @0
    wn
    #
    @1
    @5
    @6
    @1
    wn
    #
    @5
    @6
    @7
    wa
    #
    @4
    vx
    @6
    @7
    vx
    vz
    vx
    vx
    nfnae
    vz
    vy
    vx
    nfnae
    nfan
    @8
    @3
    vz
    @6
    @7
    vz
    vz
    vx
    vz
    nfnae
    vz
    vy
    vz
    nfnae
    nfan
    @6
    @7
    @3
    vx
    vy
    vz
    axc9
    imp
    alrimi
    alrimi
    ex
    orrd
    orri
end
