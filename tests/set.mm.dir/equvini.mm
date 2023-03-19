include "weq.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "equtr.mm"
include "equeuclr.mm"
include "anc2ri.mm"
include "syli.mm"
include "19.8a.mm"
include "syl6.mm"
include "wn.mm"
include "wal.mm"
include "ax13.mm"
include "ax6e.mm"
include "eximii.mm"
include "19.35i.mm"
include "pm2.61i.mm"

theorem equvini
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( x = y -> E. z ( x = z /\ z = y ) )

  proof
    vz
    vx
    weq
    #
    vx
    vy
    weq
    #
    vx
    vz
    weq
    #
    vz
    vy
    weq
    #
    wa
    #
    vz
    wex
    #
    wi
    @0
    @1
    @4
    @5
    @1
    @0
    @3
    @4
    vz
    vx
    vy
    equtr
    @3
    @1
    @2
    vz
    vx
    vy
    equeuclr
    anc2ri
    #
    syli
    @4
    vz
    19.8a
    syl6
    @0
    wn
    @1
    @1
    vz
    wal
    @5
    vz
    vx
    vy
    ax13
    @1
    @4
    vz
    @3
    @1
    @4
    wi
    vz
    vz
    vy
    ax6e
    @6
    eximii
    19.35i
    syl6
    pm2.61i
end
