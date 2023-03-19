include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wel.mm"
include "wi.mm"
include "equvinv.mm"
include "ax8v2.mm"
include "equcoms.mm"
include "ax8v1.mm"
include "sylan9.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem ax8
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t


  assert |- ( x = y -> ( x e. z -> y e. z ) )

  proof
    vx
    vy
    weq
    vt
    vx
    weq
    #
    vt
    vy
    weq
    #
    wa
    #
    vt
    wex
    vx
    vz
    wel
    #
    vy
    vz
    wel
    #
    wi
    #
    vx
    vy
    vt
    equvinv
    @2
    @5
    vt
    @0
    @3
    vt
    vz
    wel
    #
    @1
    @4
    @3
    @6
    wi
    vx
    vt
    vx
    vt
    vz
    ax8v2
    equcoms
    vt
    vy
    vz
    ax8v1
    sylan9
    exlimiv
    sylbi
end
