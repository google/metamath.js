include "weq.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wb.mm"
include "cv.mm"
include "ax-ext.mm"
include "df-cleq.mm"
include "biimpi.mm"
include "biimp.mm"
include "sylg.mm"
include "ax8v2.mm"
include "equcoms.mm"
include "ax8v1.mm"
include "imim12d.mm"
include "spimvw.mm"
include "syl.mm"

theorem bj-ax9-2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( x = y -> ( z e. x -> z e. y ) )

  proof
    vx
    vy
    weq
    #
    vu
    vx
    wel
    #
    vu
    vy
    wel
    #
    wi
    #
    vu
    wal
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wi
    #
    @0
    @1
    @2
    wb
    #
    @3
    vu
    @0
    @7
    vu
    wal
    vu
    vv
    vw
    vx
    cv
    vy
    cv
    vv
    vw
    vu
    ax-ext
    df-cleq
    biimpi
    @1
    @2
    biimp
    sylg
    @3
    @6
    vu
    vz
    vu
    vz
    weq
    @4
    @1
    @2
    @5
    @4
    @1
    wi
    vz
    vu
    vz
    vu
    vx
    ax8v2
    equcoms
    vu
    vz
    vy
    ax8v1
    imim12d
    spimvw
    syl
end
