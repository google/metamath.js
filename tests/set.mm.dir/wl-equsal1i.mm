include "wnf.mm"
include "wo.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "gen2.mm"
include "sp.mm"
include "alcoms.mm"
include "wl-equsal1t.mm"
include "syl5ib.mm"
include "wl-equsalcom.mm"
include "biimpd.mm"
include "syl5bir.mm"
include "spsd.mm"
include "jaoi.mm"
include "mp2.mm"

theorem wl-equsal1i
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume wl-equsal1i.1: |- ( F/ x ph \/ F/ y ph )
  assume wl-equsal1i.2: |- ( x = y -> ph )


  assert |- ph

  proof
    wph
    vx
    wnf
    #
    wph
    vy
    wnf
    #
    wo
    vx
    vy
    weq
    wph
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    wph
    wl-equsal1i.1
    @2
    vx
    vy
    wl-equsal1i.2
    gen2
    @0
    @4
    wph
    wi
    @1
    @4
    @2
    vx
    wal
    #
    @0
    wph
    @2
    @5
    vy
    vx
    @5
    vy
    sp
    alcoms
    wph
    vx
    vy
    wl-equsal1t
    syl5ib
    @1
    @3
    wph
    vx
    @3
    vy
    vx
    weq
    wph
    wi
    vy
    wal
    #
    @1
    wph
    wph
    vy
    vx
    wl-equsalcom
    @1
    @6
    wph
    wph
    vy
    vx
    wl-equsal1t
    biimpd
    syl5bir
    spsd
    jaoi
    mp2
end
