include "cv.mm"
include "wnfc.mm"
include "wel.mm"
include "wb.mm"
include "wal.mm"
include "weq.mm"
include "dtru.mm"
include "ax-ext.mm"
include "sps.mm"
include "alimi.mm"
include "mto.mm"
include "wnf.mm"
include "df-nfc.mm"
include "wsb.mm"
include "sbnf2.mm"
include "elsb4.mm"
include "bibi12i.mm"
include "2albii.mm"
include "bitri.mm"
include "albii.mm"
include "alrot3.mm"
include "3bitri.mm"
include "mtbir.mm"

theorem nfnid
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z


  assert |- -. F/_ x x

  proof
    vx
    vx
    cv
    #
    wnfc
    #
    vy
    vz
    wel
    #
    vy
    vw
    wel
    #
    wb
    #
    vy
    wal
    #
    vw
    wal
    #
    vz
    wal
    #
    @7
    vz
    vw
    weq
    #
    vz
    wal
    vz
    vw
    dtru
    @6
    @8
    vz
    @5
    @8
    vw
    vz
    vw
    vy
    ax-ext
    sps
    alimi
    mto
    @1
    vy
    vx
    wel
    #
    vx
    wnf
    #
    vy
    wal
    @4
    vw
    wal
    vz
    wal
    #
    vy
    wal
    @7
    vx
    vy
    @0
    df-nfc
    @10
    @11
    vy
    @10
    @9
    vx
    vz
    wsb
    #
    @9
    vx
    vw
    wsb
    #
    wb
    #
    vw
    wal
    vz
    wal
    @11
    @9
    vx
    vz
    vw
    sbnf2
    @14
    @4
    vz
    vw
    @12
    @2
    @13
    @3
    vz
    vx
    vy
    elsb4
    vw
    vx
    vy
    elsb4
    bibi12i
    2albii
    bitri
    albii
    @4
    vy
    vz
    vw
    alrot3
    3bitri
    mtbir
end
