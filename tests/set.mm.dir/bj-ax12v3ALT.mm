include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-5.mm"
include "axc11r.mm"
include "ala1.mm"
include "syl56.mm"
include "a1d.mm"
include "axc15.mm"
include "pm2.61i.mm"

theorem bj-ax12v3ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( x = y -> ( ph -> A. x ( x = y -> ph ) ) )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    @0
    wph
    @0
    wph
    wi
    vx
    wal
    #
    wi
    #
    wi
    @1
    @3
    @0
    wph
    wph
    vy
    wal
    @1
    wph
    vx
    wal
    @2
    wph
    vy
    ax-5
    wph
    vy
    vx
    axc11r
    wph
    @0
    vx
    ala1
    syl56
    a1d
    wph
    vx
    vy
    axc15
    pm2.61i
end
