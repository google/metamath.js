include "weq.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "wal.mm"
include "wo.mm"
include "simpl.mm"
include "pm2.27.mm"
include "anc2li.mm"
include "sps.mm"
include "olc.mm"
include "syl56.mm"
include "wn.mm"
include "simpr.mm"
include "equs5.mm"
include "biimpd.mm"
include "orc.mm"
include "pm2.61i.mm"
include "sp.mm"
include "pm3.4.mm"
include "jaoi.mm"
include "equs4.mm"
include "19.8a.mm"
include "jca.mm"
include "impbii.mm"

theorem bj-sbsb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( x = y -> ph ) /\ E. x ( x = y /\ ph ) ) <-> ( A. x ( x = y -> ph ) \/ ( x = y /\ ph ) ) )

  proof
    vx
    vy
    weq
    #
    wph
    wi
    #
    @0
    wph
    wa
    #
    vx
    wex
    #
    wa
    #
    @1
    vx
    wal
    #
    @2
    wo
    #
    @0
    vx
    wal
    #
    @4
    @6
    wi
    @4
    @1
    @7
    @2
    @6
    @1
    @3
    simpl
    @0
    @1
    @2
    wi
    vx
    @0
    @1
    wph
    @0
    wph
    pm2.27
    anc2li
    sps
    @2
    @5
    olc
    syl56
    @4
    @3
    @7
    wn
    #
    @5
    @6
    @1
    @3
    simpr
    @8
    @3
    @5
    wph
    vx
    vy
    equs5
    biimpd
    @5
    @2
    orc
    syl56
    pm2.61i
    @6
    @1
    @3
    @5
    @1
    @2
    @1
    vx
    sp
    @0
    wph
    pm3.4
    jaoi
    @5
    @3
    @2
    wph
    vx
    vy
    equs4
    @2
    vx
    19.8a
    jaoi
    jca
    impbii
end
