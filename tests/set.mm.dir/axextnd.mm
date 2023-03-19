include "wel.mm"
include "wb.mm"
include "weq.mm"
include "wal.mm"
include "wex.mm"
include "wi.mm"
include "wn.mm"
include "wa.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfcrd.mm"
include "adantl.mm"
include "nfbid.mm"
include "elequ1.mm"
include "bibi12d.mm"
include "a1i.mm"
include "cbvald.mm"
include "axext3.mm"
include "syl6bir.mm"
include "19.8a.mm"
include "syl6.mm"
include "ex.mm"
include "ax6e.mm"
include "ax7.mm"
include "aleximi.mm"
include "mpi.mm"
include "a1d.mm"
include "equcomi.mm"
include "pm2.61ii.mm"
include "19.35ri.mm"

theorem axextnd
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- E. x ( ( x e. y <-> x e. z ) -> y = z )

  proof
    vx
    vy
    wel
    #
    vx
    vz
    wel
    #
    wb
    #
    vy
    vz
    weq
    #
    vx
    vx
    vy
    weq
    #
    vx
    wal
    #
    vx
    vz
    weq
    #
    vx
    wal
    #
    @2
    vx
    wal
    #
    @3
    vx
    wex
    #
    wi
    #
    @5
    wn
    #
    @7
    wn
    #
    @10
    @11
    @12
    wa
    #
    @8
    @3
    @9
    @13
    @8
    vw
    vy
    wel
    #
    vw
    vz
    wel
    #
    wb
    #
    vw
    wal
    @3
    @13
    @16
    @2
    vw
    vx
    @11
    @12
    vx
    vx
    vy
    vx
    nfnae
    vx
    vz
    vx
    nfnae
    nfan
    @13
    @14
    @15
    vx
    @13
    vx
    vw
    vy
    cv
    #
    @11
    vx
    @17
    wnfc
    @12
    vx
    vy
    nfcvf
    adantr
    nfcrd
    @13
    vx
    vw
    vz
    cv
    #
    @12
    vx
    @18
    wnfc
    @11
    vx
    vz
    nfcvf
    adantl
    nfcrd
    nfbid
    vw
    vx
    weq
    #
    @16
    @2
    wb
    wi
    @13
    @19
    @14
    @0
    @15
    @1
    vw
    vx
    vy
    elequ1
    vw
    vx
    vz
    elequ1
    bibi12d
    a1i
    cbvald
    vy
    vz
    vw
    axext3
    syl6bir
    @3
    vx
    19.8a
    syl6
    ex
    @5
    @9
    @8
    @5
    @6
    vx
    wex
    @9
    vx
    vz
    ax6e
    @4
    @6
    @3
    vx
    vx
    vy
    vz
    ax7
    aleximi
    mpi
    a1d
    @7
    @9
    @8
    @7
    @4
    vx
    wex
    @9
    vx
    vy
    ax6e
    @6
    @4
    @3
    vx
    @6
    @4
    vz
    vy
    weq
    @3
    vx
    vz
    vy
    ax7
    vz
    vy
    equcomi
    syl6
    aleximi
    mpi
    a1d
    pm2.61ii
    19.35ri
end
