include "weq.mm"
include "wel.mm"
include "ax8.mm"
include "wi.mm"
include "equcoms.mm"
include "impbid.mm"

theorem elequ1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> ( x e. z <-> y e. z ) )

  proof
    vx
    vy
    weq
    vx
    vz
    wel
    #
    vy
    vz
    wel
    #
    vx
    vy
    vz
    ax8
    @1
    @0
    wi
    vy
    vx
    vy
    vx
    vz
    ax8
    equcoms
    impbid
end
