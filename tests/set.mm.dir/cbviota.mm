include "weq.mm"
include "wb.mm"
include "wal.mm"
include "cab.mm"
include "cuni.mm"
include "cio.mm"
include "wsb.mm"
include "nfv.mm"
include "nfs1v.mm"
include "nfbi.mm"
include "sbequ12.mm"
include "equequ1.mm"
include "bibi12d.mm"
include "cbval.mm"
include "nfsb.mm"
include "sbequ.mm"
include "sbie.mm"
include "syl6bb.mm"
include "bitri.mm"
include "abbii.mm"
include "unieqi.mm"
include "dfiota2.mm"
include "3eqtr4i.mm"

theorem cbviota
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume cbviota.1: |- ( x = y -> ( ph <-> ps ) )
  assume cbviota.2: |- F/ y ph
  assume cbviota.3: |- F/ x ps


  assert |- ( iota x ph ) = ( iota y ps )

  proof
    wph
    vx
    vw
    weq
    #
    wb
    #
    vx
    wal
    #
    vw
    cab
    #
    cuni
    wps
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
    cab
    #
    cuni
    wph
    vx
    cio
    wps
    vy
    cio
    @3
    @7
    @2
    @6
    vw
    @2
    wph
    vx
    vz
    wsb
    #
    vz
    vw
    weq
    #
    wb
    #
    vz
    wal
    @6
    @1
    @10
    vx
    vz
    @1
    vz
    nfv
    @8
    @9
    vx
    wph
    vx
    vz
    nfs1v
    @9
    vx
    nfv
    nfbi
    vx
    vz
    weq
    wph
    @8
    @0
    @9
    wph
    vx
    vz
    sbequ12
    vx
    vz
    vw
    equequ1
    bibi12d
    cbval
    @10
    @5
    vz
    vy
    @8
    @9
    vy
    wph
    vx
    vz
    vy
    cbviota.2
    nfsb
    @9
    vy
    nfv
    nfbi
    @5
    vz
    nfv
    vz
    vy
    weq
    #
    @8
    wps
    @9
    @4
    @11
    @8
    wph
    vx
    vy
    wsb
    wps
    wph
    vz
    vy
    vx
    sbequ
    wph
    wps
    vx
    vy
    cbviota.3
    cbviota.1
    sbie
    syl6bb
    vz
    vy
    vw
    equequ1
    bibi12d
    cbval
    bitri
    abbii
    unieqi
    wph
    vx
    vw
    dfiota2
    wps
    vy
    vw
    dfiota2
    3eqtr4i
end
