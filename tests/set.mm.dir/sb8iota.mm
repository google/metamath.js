include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "wsb.mm"
include "cio.mm"
include "nfv.mm"
include "sb8.mm"
include "sbbi.mm"
include "nfsb.mm"
include "equsb3.mm"
include "nfxfr.mm"
include "nfbi.mm"
include "sbequ.mm"
include "cbval.mm"
include "sblbis.mm"
include "albii.mm"
include "3bitri.mm"
include "abbii.mm"
include "unieqi.mm"
include "dfiota2.mm"
include "3eqtr4i.mm"

theorem sb8iota
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume sb8iota.1: |- F/ y ph


  assert |- ( iota x ph ) = ( iota y [ y / x ] ph )

  proof
    wph
    vx
    vz
    weq
    #
    wb
    #
    vx
    wal
    #
    vz
    cab
    #
    cuni
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    weq
    #
    wb
    #
    vy
    wal
    #
    vz
    cab
    #
    cuni
    wph
    vx
    cio
    @4
    vy
    cio
    @3
    @8
    @2
    @7
    vz
    @2
    @1
    vx
    vw
    wsb
    #
    vw
    wal
    @1
    vx
    vy
    wsb
    #
    vy
    wal
    @7
    @1
    vx
    vw
    @1
    vw
    nfv
    sb8
    @9
    @10
    vw
    vy
    @9
    wph
    vx
    vw
    wsb
    #
    @0
    vx
    vw
    wsb
    #
    wb
    vy
    wph
    @0
    vx
    vw
    sbbi
    @11
    @12
    vy
    wph
    vx
    vw
    vy
    sb8iota.1
    nfsb
    @12
    vw
    vz
    weq
    #
    vy
    vw
    vx
    vz
    equsb3
    @13
    vy
    nfv
    nfxfr
    nfbi
    nfxfr
    @10
    vw
    nfv
    @1
    vw
    vy
    vx
    sbequ
    cbval
    @10
    @6
    vy
    @0
    @5
    wph
    vx
    vy
    vy
    vx
    vz
    equsb3
    sblbis
    albii
    3bitri
    abbii
    unieqi
    wph
    vx
    vz
    dfiota2
    @4
    vy
    vz
    dfiota2
    3eqtr4i
end
