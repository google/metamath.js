include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wnf.mm"
include "axc16nf.mm"
include "nfsb4.mm"
include "pm2.61i.mm"

theorem nfsb
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  assume nfsb.1: |- F/ z ph

  disjoint y z
  assert |- F/ z [ y / x ] ph

  proof
    vz
    vy
    weq
    vz
    wal
    wph
    vx
    vy
    wsb
    #
    vz
    wnf
    @0
    vz
    vy
    vz
    axc16nf
    wph
    vx
    vy
    vz
    nfsb.1
    nfsb4
    pm2.61i
end
