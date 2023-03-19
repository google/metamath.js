include "wel.mm"
include "wb.mm"
include "wi.mm"
include "wex.mm"
include "weq.mm"
include "axextnd.mm"
include "ax8.mm"
include "imim2i.mm"
include "eximii.mm"
include "biimpexp.mm"
include "exbii.mm"
include "mpbi.mm"

theorem axextdfeq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- E. z ( ( z e. x -> z e. y ) -> ( ( z e. y -> z e. x ) -> ( x e. w -> y e. w ) ) )

  proof
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wb
    #
    vx
    vw
    wel
    vy
    vw
    wel
    wi
    #
    wi
    #
    vz
    wex
    @0
    @1
    wi
    @1
    @0
    wi
    @3
    wi
    wi
    #
    vz
    wex
    @2
    vx
    vy
    weq
    #
    wi
    @4
    vz
    vz
    vx
    vy
    axextnd
    @6
    @3
    @2
    vx
    vy
    vw
    ax8
    imim2i
    eximii
    @4
    @5
    vz
    @0
    @1
    @3
    biimpexp
    exbii
    mpbi
end
