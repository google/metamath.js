include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wel.mm"
include "wb.mm"
include "nfnae.mm"
include "nfan.mm"
include "cv.mm"
include "wnfc.mm"
include "nfcvf.mm"
include "adantr.mm"
include "nfcrd.mm"
include "adantl.mm"
include "nfbid.mm"
include "wi.mm"
include "elequ1.mm"
include "bibi12d.mm"
include "a1i.mm"
include "cbvald.mm"
include "axext3.mm"
include "syl6bir.mm"

theorem axextdist
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( -. A. z z = x /\ -. A. z z = y ) -> ( A. z ( z e. x <-> z e. y ) -> x = y ) )

  proof
    vz
    vx
    weq
    vz
    wal
    wn
    #
    vz
    vy
    weq
    vz
    wal
    wn
    #
    wa
    #
    vz
    vx
    wel
    #
    vz
    vy
    wel
    #
    wb
    #
    vz
    wal
    vw
    vx
    wel
    #
    vw
    vy
    wel
    #
    wb
    #
    vw
    wal
    vx
    vy
    weq
    @2
    @8
    @5
    vw
    vz
    @0
    @1
    vz
    vz
    vx
    vz
    nfnae
    vz
    vy
    vz
    nfnae
    nfan
    @2
    @6
    @7
    vz
    @2
    vz
    vw
    vx
    cv
    #
    @0
    vz
    @9
    wnfc
    @1
    vz
    vx
    nfcvf
    adantr
    nfcrd
    @2
    vz
    vw
    vy
    cv
    #
    @1
    vz
    @10
    wnfc
    @0
    vz
    vy
    nfcvf
    adantl
    nfcrd
    nfbid
    vw
    vz
    weq
    #
    @8
    @5
    wb
    wi
    @2
    @11
    @6
    @3
    @7
    @4
    vw
    vz
    vx
    elequ1
    vw
    vz
    vy
    elequ1
    bibi12d
    a1i
    cbvald
    vx
    vy
    vw
    axext3
    syl6bir
end
