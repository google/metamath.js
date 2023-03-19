include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "wa.mm"
include "equtr2.mm"
include "equcomd.mm"
include "ax12v.mm"
include "syl.mm"
include "expimpd.mm"
include "com12.mm"
include "alrimiv.mm"
include "ex.mm"
include "df-ssb.mm"
include "syl6ibr.mm"

theorem bj-ssbequ1
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( x = t -> ( ph -> [b t /b x ]b ph ) )

  proof
    vx
    vt
    weq
    #
    wph
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    wph
    vx
    vt
    wssb
    @0
    wph
    @5
    @0
    wph
    wa
    #
    @4
    vy
    @1
    @6
    @3
    @1
    @0
    wph
    @3
    @1
    @0
    wa
    #
    @2
    wph
    @3
    wi
    @7
    vy
    vx
    vy
    vx
    vt
    equtr2
    equcomd
    wph
    vx
    vy
    ax12v
    syl
    expimpd
    com12
    alrimiv
    ex
    wph
    vx
    vy
    vt
    df-ssb
    syl6ibr
end
