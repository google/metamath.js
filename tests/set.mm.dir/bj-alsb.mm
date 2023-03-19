include "wal.mm"
include "weq.mm"
include "wi.mm"
include "wssb.mm"
include "ala1.mm"
include "a1d.mm"
include "alrimiv.mm"
include "df-ssb.mm"
include "sylibr.mm"

theorem bj-alsb
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
  let vy: setvar y


  assert |- ( A. x ph -> [b t /b x ]b ph )

  proof
    wph
    vx
    wal
    #
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
    wph
    vx
    vt
    wssb
    @0
    @4
    vy
    @0
    @3
    @1
    wph
    @2
    vx
    ala1
    a1d
    alrimiv
    wph
    vx
    vy
    vt
    df-ssb
    sylibr
end
