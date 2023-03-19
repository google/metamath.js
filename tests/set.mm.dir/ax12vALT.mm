include "weq.mm"
include "wal.mm"
include "wi.mm"
include "ax-1.mm"
include "axc16.mm"
include "syl5.mm"
include "a1d.mm"
include "axc15.mm"
include "pm2.61i.mm"

theorem ax12vALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
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
    #
    vx
    wal
    #
    wi
    #
    wi
    @1
    @4
    @0
    wph
    @2
    @1
    @3
    wph
    @0
    ax-1
    @2
    vx
    vy
    axc16
    syl5
    a1d
    wph
    vx
    vy
    axc15
    pm2.61i
end
