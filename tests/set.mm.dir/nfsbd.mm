include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wnf.mm"
include "wn.mm"
include "wi.mm"
include "alrimi.mm"
include "nfsb4t.mm"
include "syl.mm"
include "axc16nf.mm"
include "pm2.61d2.mm"

theorem nfsbd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume nfsbd.1: |- F/ x ph
  assume nfsbd.2: |- ( ph -> F/ z ps )

  disjoint y z
  assert |- ( ph -> F/ z [ y / x ] ps )

  proof
    wph
    vz
    vy
    weq
    vz
    wal
    #
    wps
    vx
    vy
    wsb
    #
    vz
    wnf
    #
    wph
    wps
    vz
    wnf
    #
    vx
    wal
    @0
    wn
    @2
    wi
    wph
    @3
    vx
    nfsbd.1
    nfsbd.2
    alrimi
    wps
    vx
    vy
    vz
    nfsb4t
    syl
    @1
    vz
    vy
    vz
    axc16nf
    pm2.61d2
end
