include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wb.mm"
include "drsb1.mm"
include "nfae.mm"
include "sbequ12a.mm"
include "sps.mm"
include "sbbid.mm"
include "bitr3d.mm"
include "wn.mm"
include "sbco.mm"
include "sbbii.mm"
include "nfnae.mm"
include "nfsb2.mm"
include "sbco2d.mm"
include "syl5rbbr.mm"
include "pm2.61i.mm"

theorem sbco3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ x / y ] ph )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    wsb
    #
    wph
    vy
    vx
    wsb
    #
    vx
    vz
    wsb
    #
    wb
    @1
    @2
    vx
    vz
    wsb
    @3
    @5
    @2
    vx
    vy
    vz
    drsb1
    @1
    @2
    @4
    vx
    vz
    vx
    vy
    vx
    nfae
    @0
    @2
    @4
    wb
    vx
    wph
    vx
    vy
    sbequ12a
    sps
    sbbid
    bitr3d
    @5
    @2
    vy
    vx
    wsb
    #
    vx
    vz
    wsb
    @1
    wn
    #
    @3
    @6
    @4
    vx
    vz
    wph
    vy
    vx
    sbco
    sbbii
    @7
    @2
    vy
    vz
    vx
    vx
    vy
    vy
    nfnae
    vx
    vy
    vx
    nfnae
    wph
    vx
    vy
    nfsb2
    sbco2d
    syl5rbbr
    pm2.61i
end
