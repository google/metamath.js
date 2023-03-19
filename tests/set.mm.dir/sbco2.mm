include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wb.mm"
include "sbequ12.mm"
include "sbequ.mm"
include "bitr3d.mm"
include "sps.mm"
include "wn.mm"
include "nfnae.mm"
include "nfsb4.mm"
include "wi.mm"
include "a1i.mm"
include "sbied.mm"
include "pm2.61i.mm"

theorem sbco2
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assume sbco2.1: |- F/ z ph


  assert |- ( [ y / z ] [ z / x ] ph <-> [ y / x ] ph )

  proof
    vz
    vy
    weq
    #
    vz
    wal
    #
    wph
    vx
    vz
    wsb
    #
    vz
    vy
    wsb
    #
    wph
    vx
    vy
    wsb
    #
    wb
    #
    @0
    @5
    vz
    @0
    @2
    @3
    @4
    @2
    vz
    vy
    sbequ12
    wph
    vz
    vy
    vx
    sbequ
    #
    bitr3d
    sps
    @1
    wn
    #
    @2
    @4
    vz
    vy
    vz
    vy
    vz
    nfnae
    wph
    vx
    vy
    vz
    sbco2.1
    nfsb4
    @0
    @2
    @4
    wb
    wi
    @7
    @6
    a1i
    sbied
    pm2.61i
end
