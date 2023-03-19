include "weq.mm"
include "wal.mm"
include "wi.mm"
include "wa.mm"
include "aeveq.mm"
include "adantl.mm"
include "a1d.mm"
include "wn.mm"
include "ax13v.mm"
include "equtrr.mm"
include "al2imi.mm"
include "con3d.mm"
include "syl6.mm"
include "com13.mm"
include "impcom.mm"
include "con4d.mm"
include "pm2.61dan.mm"
include "ax6evr.mm"
include "exlimiiv.mm"

theorem wl-spae
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x x = y -> x = y )

  proof
    vy
    vz
    weq
    #
    vx
    vy
    weq
    #
    vx
    wal
    #
    @1
    wi
    #
    vz
    @0
    vx
    vz
    weq
    #
    vx
    wal
    #
    @3
    @0
    @5
    wa
    @1
    @2
    @5
    @1
    @0
    vx
    vz
    vx
    vy
    aeveq
    adantl
    a1d
    @0
    @5
    wn
    #
    wa
    @1
    @2
    @6
    @0
    @1
    wn
    #
    @2
    wn
    #
    wi
    @7
    @0
    @6
    @8
    @7
    @0
    @0
    vx
    wal
    #
    @6
    @8
    wi
    vx
    vy
    vz
    ax13v
    @9
    @2
    @5
    @0
    @1
    @4
    vx
    vy
    vz
    vx
    equtrr
    al2imi
    con3d
    syl6
    com13
    impcom
    con4d
    pm2.61dan
    vz
    vy
    ax6evr
    exlimiiv
end
