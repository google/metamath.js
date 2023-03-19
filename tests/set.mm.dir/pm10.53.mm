include "wex.mm"
include "wn.mm"
include "wal.mm"
include "wi.mm"
include "pm2.21.mm"
include "19.38.mm"
include "syl.mm"

theorem pm10.53
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( -. E. x ph -> A. x ( ph -> ps ) )

  proof
    wph
    vx
    wex
    #
    wn
    @0
    wps
    vx
    wal
    #
    wi
    wph
    wps
    wi
    vx
    wal
    @0
    @1
    pm2.21
    wph
    wps
    vx
    19.38
    syl
end
