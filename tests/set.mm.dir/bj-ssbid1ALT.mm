include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "ax12v.mm"
include "equcoms.mm"
include "com12.mm"
include "alrimiv.mm"
include "df-ssb.mm"
include "sylibr.mm"

theorem bj-ssbid1ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( ph -> [b x /b x ]b ph )

  proof
    wph
    vy
    vx
    weq
    #
    vx
    vy
    weq
    wph
    wi
    vx
    wal
    #
    wi
    #
    vy
    wal
    wph
    vx
    vx
    wssb
    wph
    @2
    vy
    @0
    wph
    @1
    wph
    @1
    wi
    vx
    vy
    wph
    vx
    vy
    ax12v
    equcoms
    com12
    alrimiv
    wph
    vx
    vy
    vx
    df-ssb
    sylibr
end
