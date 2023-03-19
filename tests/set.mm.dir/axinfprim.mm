include "wel.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "axinfnd.mm"
include "df-an.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"
include "imbi2i.mm"
include "albii.mm"
include "anbi2i.mm"
include "df-ex.mm"
include "mpbi.mm"

theorem axinfprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A. x -. ( y e. z -> -. ( y e. x -> -. A. y ( y e. x -> -. A. z ( y e. z -> -. z e. x ) ) ) )

  proof
    vy
    vz
    wel
    #
    vy
    vx
    wel
    #
    @1
    @0
    vz
    vx
    wel
    #
    wa
    #
    vz
    wex
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    wi
    #
    vx
    wex
    #
    @0
    @1
    @1
    @0
    @2
    wn
    wi
    #
    vz
    wal
    wn
    #
    wi
    #
    vy
    wal
    #
    wn
    wi
    wn
    #
    wi
    #
    wn
    vx
    wal
    wn
    #
    vx
    vy
    vz
    axinfnd
    @9
    @15
    vx
    wex
    @16
    @8
    @15
    vx
    @7
    @14
    @0
    @7
    @1
    @13
    wa
    @14
    @6
    @13
    @1
    @5
    @12
    vy
    @4
    @11
    @1
    @4
    @10
    wn
    #
    vz
    wex
    @11
    @3
    @17
    vz
    @0
    @2
    df-an
    exbii
    @10
    vz
    exnal
    bitri
    imbi2i
    albii
    anbi2i
    @1
    @13
    df-an
    bitri
    imbi2i
    exbii
    @15
    vx
    df-ex
    bitri
    mpbi
end
