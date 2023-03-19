include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "wn.mm"
include "axrepnd.mm"
include "df-ex.mm"
include "df-an.mm"
include "exbii.mm"
include "exnal.mm"
include "bitri.mm"
include "bibi2i.mm"
include "dfbi1.mm"
include "albii.mm"
include "imbi12i.mm"
include "mpbi.mm"

theorem axrepprim
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A. x -. ( -. A. y -. A. z ( ph -> z = y ) -> A. z -. ( ( A. y z e. x -> -. A. x ( A. z x e. y -> -. A. y ph ) ) -> -. ( -. A. x ( A. z x e. y -> -. A. y ph ) -> A. y z e. x ) ) )

  proof
    wph
    vz
    vy
    weq
    wi
    vz
    wal
    #
    vy
    wex
    #
    vz
    vx
    wel
    vy
    wal
    #
    vx
    vy
    wel
    vz
    wal
    #
    wph
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    wb
    #
    vz
    wal
    #
    wi
    #
    vx
    wex
    #
    @0
    wn
    vy
    wal
    wn
    #
    @2
    @3
    @4
    wn
    wi
    #
    vx
    wal
    wn
    #
    wi
    @13
    @2
    wi
    wn
    wi
    wn
    #
    vz
    wal
    #
    wi
    #
    wn
    vx
    wal
    wn
    #
    wph
    vx
    vy
    vz
    axrepnd
    @10
    @16
    vx
    wex
    @17
    @9
    @16
    vx
    @1
    @11
    @8
    @15
    @0
    vy
    df-ex
    @7
    @14
    vz
    @7
    @2
    @13
    wb
    @14
    @6
    @13
    @2
    @6
    @12
    wn
    #
    vx
    wex
    @13
    @5
    @18
    vx
    @3
    @4
    df-an
    exbii
    @12
    vx
    exnal
    bitri
    bibi2i
    @2
    @13
    dfbi1
    bitri
    albii
    imbi12i
    exbii
    @16
    vx
    df-ex
    bitri
    mpbi
end
