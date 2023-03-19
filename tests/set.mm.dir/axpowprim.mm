include "weq.mm"
include "wel.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "wex.mm"
include "axpownd.mm"
include "df-ex.mm"
include "imbi1i.mm"
include "albii.mm"
include "exbii.mm"
include "bitri.mm"
include "sylib.mm"
include "con4i.mm"

theorem axpowprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x -. A. y ( A. x ( -. A. z -. x e. y -> A. y x e. z ) -> y e. x ) -> x = y )

  proof
    vx
    vy
    weq
    #
    vx
    vy
    wel
    #
    wn
    vz
    wal
    wn
    #
    vx
    vz
    wel
    vy
    wal
    #
    wi
    #
    vx
    wal
    #
    vy
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    wn
    vx
    wal
    #
    @0
    wn
    @1
    vz
    wex
    #
    @3
    wi
    #
    vx
    wal
    #
    @6
    wi
    #
    vy
    wal
    #
    vx
    wex
    #
    @9
    wn
    #
    vx
    vy
    vz
    axpownd
    @15
    @8
    vx
    wex
    @16
    @14
    @8
    vx
    @13
    @7
    vy
    @12
    @5
    @6
    @11
    @4
    vx
    @10
    @2
    @3
    @1
    vz
    df-ex
    imbi1i
    albii
    imbi1i
    albii
    exbii
    @8
    vx
    df-ex
    bitri
    sylib
    con4i
end
