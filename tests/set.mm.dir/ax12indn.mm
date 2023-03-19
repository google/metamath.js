include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wex.mm"
include "19.8a.mm"
include "exanali.mm"
include "hbn1.mm"
include "con3.mm"
include "syl6.mm"
include "com23.mm"
include "alrimdh.mm"
include "syl5bi.mm"
include "syl5.mm"
include "expd.mm"

theorem ax12indn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume ax12indn.1: |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )


  assert |- ( -. A. x x = y -> ( x = y -> ( -. ph -> A. x ( x = y -> -. ph ) ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @0
    wph
    wn
    #
    @0
    @2
    wi
    #
    vx
    wal
    #
    @0
    @2
    wa
    #
    @5
    vx
    wex
    #
    @1
    @4
    @5
    vx
    19.8a
    @6
    @0
    wph
    wi
    #
    vx
    wal
    #
    wn
    #
    @1
    @4
    @0
    wph
    vx
    exanali
    @1
    @9
    @3
    vx
    @0
    vx
    hbn1
    @7
    vx
    hbn1
    @1
    @0
    @9
    @2
    @1
    @0
    wph
    @8
    wi
    @9
    @2
    wi
    ax12indn.1
    wph
    @8
    con3
    syl6
    com23
    alrimdh
    syl5bi
    syl5
    expd
end
