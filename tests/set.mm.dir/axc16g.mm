include "weq.mm"
include "wal.mm"
include "wi.mm"
include "aevlem.mm"
include "ax12v.mm"
include "sps.mm"
include "pm2.27.mm"
include "al2imi.mm"
include "syld.mm"
include "syl.mm"

theorem axc16g
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  assert |- ( A. x x = y -> ( ph -> A. z ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    vz
    vw
    weq
    #
    vz
    wal
    #
    wph
    wph
    vz
    wal
    #
    wi
    vx
    vy
    vz
    vw
    aevlem
    @1
    wph
    @0
    wph
    wi
    #
    vz
    wal
    #
    @2
    @0
    wph
    @4
    wi
    vz
    wph
    vz
    vw
    ax12v
    sps
    @0
    @3
    wph
    vz
    @0
    wph
    pm2.27
    al2imi
    syld
    syl
end
