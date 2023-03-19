include "weq.mm"
include "wel.mm"
include "wb.mm"
include "wex.mm"
include "wi.mm"
include "wa.mm"
include "axextnd.mm"
include "elequ2.mm"
include "jctl.mm"
include "eximii.mm"
include "dfbi2.mm"
include "exbii.mm"
include "mpbir.mm"

theorem axextndbi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- E. z ( x = y <-> ( z e. x <-> z e. y ) )

  proof
    vx
    vy
    weq
    #
    vz
    vx
    wel
    vz
    vy
    wel
    wb
    #
    wb
    #
    vz
    wex
    @0
    @1
    wi
    #
    @1
    @0
    wi
    #
    wa
    #
    vz
    wex
    @4
    @5
    vz
    vz
    vx
    vy
    axextnd
    @4
    @3
    vx
    vy
    vz
    elequ2
    jctl
    eximii
    @2
    @5
    vz
    @0
    @1
    dfbi2
    exbii
    mpbir
end
