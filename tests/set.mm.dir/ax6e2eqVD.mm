include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "idn1.mm"
include "ax6ev.mm"
include "hba1.mm"
include "sp.mm"
include "impbii.mm"
include "idn2.mm"
include "e1a.mm"
include "ax7.mm"
include "com12.mm"
include "e21.mm"
include "pm3.2.mm"
include "e22.mm"
include "in2.mm"
include "in1.mm"
include "alimi.mm"
include "sylbi.mm"
include "exim.mm"
include "pm2.27.mm"
include "e01.mm"
include "axc4i.mm"
include "axc11.mm"
include "e11.mm"
include "19.2.mm"
include "excomim.mm"
include "simpr.mm"
include "e2.mm"
include "equtrr.mm"
include "e12.mm"
include "simpl.mm"
include "pm3.21.mm"
include "gen11.mm"
include "pm2.04.mm"
include "e10.mm"

theorem ax6e2eqVD
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u

  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  assert |- ( A. x x = y -> ( u = v -> E. x E. y ( x = u /\ y = v ) ) )

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
    vu
    cv
    #
    vv
    cv
    #
    wceq
    #
    @0
    @4
    wceq
    #
    @1
    @5
    wceq
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wi
    #
    @3
    @7
    @1
    @4
    wceq
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    @6
    @16
    @11
    wi
    #
    wi
    #
    @12
    @3
    @14
    vx
    wex
    #
    vy
    wex
    #
    @16
    @3
    @19
    vy
    wal
    #
    @20
    @3
    @3
    @19
    vx
    wal
    #
    @21
    @3
    idn1
    #
    @3
    @3
    @22
    @23
    @2
    @19
    vx
    @3
    @19
    @7
    vx
    wex
    #
    @3
    @24
    @19
    wi
    #
    @19
    vx
    vu
    ax6ev
    @3
    @7
    @14
    wi
    #
    vx
    wal
    #
    @25
    @3
    @3
    @27
    @23
    @3
    @3
    vx
    wal
    #
    @27
    @3
    @28
    @2
    vx
    hba1
    @3
    vx
    sp
    impbii
    @3
    @26
    vx
    @3
    @26
    @3
    @7
    @14
    @3
    @7
    @7
    @13
    @14
    @3
    @7
    idn2
    #
    @3
    @7
    @7
    @2
    @13
    @29
    @3
    @3
    @2
    @23
    @2
    vx
    sp
    e1a
    @2
    @7
    @13
    vx
    vy
    vu
    ax7
    com12
    e21
    @7
    @13
    pm3.2
    e22
    in2
    in1
    alimi
    sylbi
    e1a
    @7
    @14
    vx
    exim
    e1a
    @24
    @19
    pm2.27
    e01
    in1
    axc4i
    e1a
    @19
    vx
    vy
    axc11
    e11
    @19
    vy
    19.2
    e1a
    @14
    vy
    vx
    excomim
    e1a
    @6
    @17
    @6
    @15
    @10
    wi
    #
    vx
    wal
    @17
    @6
    @30
    vx
    @6
    @14
    @9
    wi
    #
    vy
    wal
    @30
    @6
    @31
    vy
    @6
    @14
    @9
    @6
    @14
    @8
    @7
    @9
    @6
    @6
    @14
    @13
    @8
    @6
    idn1
    @6
    @14
    @14
    @13
    @6
    @14
    idn2
    #
    @7
    @13
    simpr
    e2
    vu
    vv
    vy
    equtrr
    e12
    @6
    @14
    @14
    @7
    @32
    @7
    @13
    simpl
    e2
    @8
    @7
    pm3.21
    e22
    in2
    gen11
    @14
    @9
    vy
    exim
    e1a
    gen11
    @15
    @10
    vx
    exim
    e1a
    in1
    @18
    @16
    @12
    @6
    @16
    @11
    pm2.04
    com12
    e10
    in1
end
