include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wa.mm"
include "wex.mm"
include "ax6e2nd.mm"
include "wi.mm"
include "ax6e2eq.mm"
include "a1d.mm"
include "pm2.61i.mm"
include "jaoi.mm"
include "olc.mm"
include "wne.mm"
include "excom.mm"
include "neeq1.mm"
include "biimprcd.mm"
include "adantrd.mm"
include "simpr.mm"
include "a1i.mm"
include "neeq2.mm"
include "syl6c.mm"
include "sp.mm"
include "necon3ai.mm"
include "syl6.mm"
include "eximdv.mm"
include "nfnae.mm"
include "19.9.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "orc.mm"
include "pm2.61ine.mm"
include "impbii.mm"

theorem ax6e2ndeq
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( ( -. A. x x = y \/ u = v ) <-> E. x E. y ( x = u /\ y = v ) )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wal
    #
    wn
    #
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    wo
    #
    @0
    @5
    wceq
    #
    @1
    @6
    wceq
    #
    wa
    #
    vy
    wex
    vx
    wex
    #
    @4
    @12
    @7
    vx
    vy
    vv
    vu
    ax6e2nd
    #
    @3
    @7
    @12
    wi
    vx
    vy
    vv
    vu
    ax6e2eq
    @4
    @12
    @7
    @13
    a1d
    pm2.61i
    jaoi
    @12
    @8
    wi
    @5
    @6
    @7
    @8
    @12
    @7
    @4
    olc
    a1d
    @5
    @6
    wne
    #
    @12
    @4
    @8
    @14
    @12
    @4
    vy
    wex
    #
    @4
    @12
    @11
    vx
    wex
    #
    vy
    wex
    @14
    @15
    @11
    vx
    vy
    excom
    @14
    @16
    @4
    vy
    @14
    @16
    @4
    vx
    wex
    @4
    @14
    @11
    @4
    vx
    @14
    @11
    @0
    @1
    wne
    #
    @4
    @14
    @11
    @0
    @6
    wne
    #
    @10
    @17
    @14
    @9
    @18
    @10
    @9
    @18
    @14
    @0
    @5
    @6
    neeq1
    biimprcd
    adantrd
    @11
    @10
    wi
    @14
    @9
    @10
    simpr
    a1i
    @10
    @17
    @18
    @1
    @6
    @0
    neeq2
    biimprcd
    syl6c
    @3
    @0
    @1
    @2
    vx
    sp
    necon3ai
    syl6
    eximdv
    @4
    vx
    vx
    vy
    vx
    nfnae
    19.9
    syl6ib
    eximdv
    syl5bi
    @4
    vy
    vx
    vy
    vy
    nfnae
    19.9
    syl6ib
    @4
    @7
    orc
    syl6
    pm2.61ine
    impbii
end
