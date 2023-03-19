include "wel.mm"
include "wa.mm"
include "wal.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wi.mm"
include "wn.mm"
include "axacnd.mm"
include "df-an.mm"
include "albii.mm"
include "anass.mm"
include "annim.mm"
include "pm4.63.mm"
include "anbi2i.mm"
include "bitr3i.mm"
include "3bitr2i.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"
include "bibi1i.mm"
include "dfbi1.mm"
include "df-ex.mm"
include "imbi12i.mm"
include "2albii.mm"
include "mpbi.mm"

theorem axacprim
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- -. A. x -. A. y A. z ( A. x -. ( y e. z -> -. z e. w ) -> -. A. w -. A. y -. ( ( -. A. w ( y e. z -> ( z e. w -> ( y e. w -> -. w e. x ) ) ) -> y = w ) -> -. ( y = w -> -. A. w ( y e. z -> ( z e. w -> ( y e. w -> -. w e. x ) ) ) ) ) )

  proof
    vy
    vz
    wel
    #
    vz
    vw
    wel
    #
    wa
    #
    vx
    wal
    #
    @2
    vy
    vw
    wel
    #
    vw
    vx
    wel
    #
    wa
    #
    wa
    #
    vw
    wex
    #
    vy
    vw
    weq
    #
    wb
    #
    vy
    wal
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
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
    wn
    #
    vx
    wal
    #
    @0
    @1
    @4
    @5
    wn
    wi
    #
    wi
    #
    wi
    #
    vw
    wal
    wn
    #
    @9
    wi
    @9
    @21
    wi
    wn
    wi
    wn
    #
    vy
    wal
    #
    wn
    vw
    wal
    wn
    #
    wi
    #
    vz
    wal
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
    vw
    axacnd
    @15
    @26
    vx
    wex
    @27
    @14
    @26
    vx
    @13
    @25
    vy
    vz
    @3
    @17
    @12
    @24
    @2
    @16
    vx
    @0
    @1
    df-an
    albii
    @12
    @23
    vw
    wex
    @24
    @11
    @23
    vw
    @10
    @22
    vy
    @10
    @21
    @9
    wb
    @22
    @8
    @21
    @9
    @8
    @20
    wn
    #
    vw
    wex
    @21
    @7
    @28
    vw
    @7
    @0
    @1
    @6
    wa
    #
    wa
    @0
    @19
    wn
    #
    wa
    @28
    @0
    @1
    @6
    anass
    @30
    @29
    @0
    @30
    @1
    @18
    wn
    #
    wa
    @29
    @1
    @18
    annim
    @31
    @6
    @1
    @4
    @5
    pm4.63
    anbi2i
    bitr3i
    anbi2i
    @0
    @19
    annim
    3bitr2i
    exbii
    @20
    vw
    exnal
    bitri
    bibi1i
    @21
    @9
    dfbi1
    bitri
    albii
    exbii
    @23
    vw
    df-ex
    bitri
    imbi12i
    2albii
    exbii
    @26
    vx
    df-ex
    bitri
    mpbi
end
