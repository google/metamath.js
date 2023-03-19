include "wel.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "axregnd.mm"
include "df-an.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"
include "sylib.mm"

theorem axregprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x e. y -> -. A. x ( x e. y -> -. A. z ( z e. x -> -. z e. y ) ) )

  proof
    vx
    vy
    wel
    #
    @0
    vz
    vx
    wel
    vz
    vy
    wel
    wn
    wi
    vz
    wal
    #
    wa
    #
    vx
    wex
    #
    @0
    @1
    wn
    wi
    #
    vx
    wal
    wn
    #
    vx
    vy
    vz
    axregnd
    @3
    @4
    wn
    #
    vx
    wex
    @5
    @2
    @6
    vx
    @0
    @1
    df-an
    exbii
    @4
    vx
    exnal
    bitri
    sylib
end
