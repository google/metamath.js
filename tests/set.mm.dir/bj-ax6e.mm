include "weq.mm"
include "wex.mm"
include "wal.mm"
include "wi.mm"
include "19.2.mm"
include "a1d.mm"
include "wn.mm"
include "bj-ax6elem1.mm"
include "bj-ax6elem2.mm"
include "syl6.mm"
include "pm2.61i.mm"
include "ax6evr.mm"
include "exlimiiv.mm"

theorem bj-ax6e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- E. x x = y

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
    wex
    #
    vz
    @1
    vx
    wal
    #
    @0
    @2
    wi
    @3
    @2
    @0
    @1
    vx
    19.2
    a1d
    @3
    wn
    @0
    @0
    vx
    wal
    @2
    vx
    vy
    vz
    bj-ax6elem1
    vx
    vy
    vz
    bj-ax6elem2
    syl6
    pm2.61i
    vz
    vy
    ax6evr
    exlimiiv
end
