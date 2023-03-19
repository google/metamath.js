include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "axc16g-o.mm"
include "syl5.mm"
include "a1d.mm"
include "ax12indalem.mm"
include "pm2.61i.mm"

theorem ax12inda2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12inda2.1: |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )

  disjoint y z
  assert |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) )

  proof
    vy
    vz
    weq
    vy
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @1
    wph
    vz
    wal
    #
    @1
    @3
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    wi
    @0
    @7
    @2
    @0
    @6
    @1
    @3
    @4
    @0
    @5
    @3
    @1
    ax-1
    @4
    vy
    vz
    vx
    axc16g-o
    syl5
    a1d
    a1d
    wph
    vx
    vy
    vz
    ax12inda2.1
    ax12indalem
    pm2.61i
end
