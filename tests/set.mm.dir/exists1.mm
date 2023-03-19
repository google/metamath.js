include "weq.mm"
include "weu.mm"
include "wb.mm"
include "wal.mm"
include "wex.mm"
include "df-eu.mm"
include "equid.mm"
include "tbt.mm"
include "bicom.mm"
include "bitri.mm"
include "albii.mm"
include "exbii.mm"
include "nfae.mm"
include "19.9.mm"
include "3bitr2i.mm"

theorem exists1
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( E! x x = x <-> A. x x = y )

  proof
    vx
    vx
    weq
    #
    vx
    weu
    @0
    vx
    vy
    weq
    #
    wb
    #
    vx
    wal
    #
    vy
    wex
    @1
    vx
    wal
    #
    vy
    wex
    @4
    @0
    vx
    vy
    df-eu
    @4
    @3
    vy
    @1
    @2
    vx
    @1
    @1
    @0
    wb
    @2
    @0
    @1
    vx
    equid
    tbt
    @1
    @0
    bicom
    bitri
    albii
    exbii
    @4
    vy
    vx
    vy
    vy
    nfae
    19.9
    3bitr2i
end
