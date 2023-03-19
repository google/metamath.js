include "weq.mm"
include "wel.mm"
include "wi.mm"
include "ax6e.mm"
include "ax8.mm"
include "equcoms.mm"
include "imim12d.mm"
include "eximii.mm"

theorem ax8dfeq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- E. z ( ( z e. x -> z e. y ) -> ( w e. x -> w e. y ) )

  proof
    vz
    vw
    weq
    #
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wi
    vw
    vx
    wel
    #
    vw
    vy
    wel
    #
    wi
    wi
    vz
    vz
    vw
    ax6e
    @0
    @3
    @1
    @2
    @4
    @3
    @1
    wi
    vw
    vz
    vw
    vz
    vx
    ax8
    equcoms
    vz
    vw
    vy
    ax8
    imim12d
    eximii
end
