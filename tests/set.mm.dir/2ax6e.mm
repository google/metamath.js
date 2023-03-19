include "weq.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "aeveq.mm"
include "jca.mm"
include "19.8a.mm"
include "3syl.mm"
include "2ax6elem.mm"
include "pm2.61i.mm"

theorem 2ax6e
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint w z
  assert |- E. z E. w ( z = x /\ w = y )

  proof
    vw
    vz
    weq
    vw
    wal
    #
    vz
    vx
    weq
    #
    vw
    vy
    weq
    #
    wa
    #
    vw
    wex
    #
    vz
    wex
    #
    @0
    @3
    @4
    @5
    @0
    @1
    @2
    vw
    vz
    vz
    vx
    aeveq
    vw
    vz
    vw
    vy
    aeveq
    jca
    @3
    vw
    19.8a
    @4
    vz
    19.8a
    3syl
    vx
    vy
    vz
    vw
    2ax6elem
    pm2.61i
end
