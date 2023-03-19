include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "axunnd.mm"
include "df-an.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"
include "imbi1i.mm"
include "albii.mm"
include "df-ex.mm"
include "mpbi.mm"

theorem axunprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A. x -. A. y ( -. A. x ( y e. x -> -. x e. z ) -> y e. x )

  proof
    vy
    vx
    wel
    #
    vx
    vz
    wel
    #
    wa
    #
    vx
    wex
    #
    @0
    wi
    #
    vy
    wal
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
    @0
    wi
    #
    vy
    wal
    #
    wn
    vx
    wal
    wn
    #
    vx
    vy
    vz
    axunnd
    @6
    @10
    vx
    wex
    @11
    @5
    @10
    vx
    @4
    @9
    vy
    @3
    @8
    @0
    @3
    @7
    wn
    #
    vx
    wex
    @8
    @2
    @12
    vx
    @0
    @1
    df-an
    exbii
    @7
    vx
    exnal
    bitri
    imbi1i
    albii
    exbii
    @10
    vx
    df-ex
    bitri
    mpbi
end
