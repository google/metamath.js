include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "copab.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wss.mm"
include "pm3.41.mm"
include "2alimi.mm"
include "adantr.mm"
include "ssopab2.mm"
include "syl.mm"
include "ssexd.mm"

theorem opabbrex
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cV: class V


  assert |- ( ( A. x A. y ( x R y -> ph ) /\ { <. x , y >. | ph } e. V ) -> { <. x , y >. | ( x R y /\ ps ) } e. _V )

  proof
    vx
    cv
    vy
    cv
    cR
    wbr
    #
    wph
    wi
    #
    vy
    wal
    vx
    wal
    #
    wph
    vx
    vy
    copab
    #
    cV
    wcel
    #
    wa
    #
    @0
    wps
    wa
    #
    vx
    vy
    copab
    #
    @3
    cV
    @2
    @4
    simpr
    @5
    @6
    wph
    wi
    #
    vy
    wal
    vx
    wal
    #
    @7
    @3
    wss
    @2
    @9
    @4
    @1
    @8
    vx
    vy
    @0
    wps
    wph
    pm3.41
    2alimi
    adantr
    @6
    wph
    vx
    vy
    ssopab2
    syl
    ssexd
end
