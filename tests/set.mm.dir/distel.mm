include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wel.mm"
include "wex.mm"
include "el.mm"
include "df-ex.mm"
include "nfnae.mm"
include "dveel1.mm"
include "nf5d.mm"
include "nfnd.mm"
include "wb.mm"
include "wi.mm"
include "elequ2.mm"
include "notbid.mm"
include "a1i.mm"
include "cbvald.mm"
include "syl5bb.mm"
include "mpbii.mm"
include "elirrv.mm"
include "elequ1.mm"
include "mtbii.mm"
include "alimi.mm"
include "con3i.mm"
include "impbii.mm"

theorem distel
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( -. A. y y = x <-> -. A. y -. x e. y )

  proof
    vy
    vx
    weq
    #
    vy
    wal
    #
    wn
    #
    vx
    vy
    wel
    #
    wn
    #
    vy
    wal
    #
    wn
    #
    @2
    vx
    vz
    wel
    #
    vz
    wex
    #
    @6
    vx
    vz
    el
    @8
    @7
    wn
    #
    vz
    wal
    #
    wn
    @2
    @6
    @7
    vz
    df-ex
    @2
    @10
    @5
    @2
    @9
    @4
    vz
    vy
    vy
    vx
    vy
    nfnae
    #
    @2
    @7
    vy
    @2
    @7
    vy
    @11
    vy
    vx
    vz
    dveel1
    nf5d
    nfnd
    vz
    vy
    weq
    #
    @9
    @4
    wb
    wi
    @2
    @12
    @7
    @3
    vz
    vy
    vx
    elequ2
    notbid
    a1i
    cbvald
    notbid
    syl5bb
    mpbii
    @1
    @5
    @0
    @4
    vy
    @0
    vy
    vy
    wel
    @3
    vy
    elirrv
    vy
    vx
    vy
    elequ1
    mtbii
    alimi
    con3i
    impbii
end
