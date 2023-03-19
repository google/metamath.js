include "wex.mm"
include "wn.mm"
include "wal.mm"
include "weq.mm"
include "wi.mm"
include "alnex.mm"
include "pm2.21.mm"
include "alimi.mm"
include "sylbir.mm"

theorem wl-lem-nexmo
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z


  assert |- ( -. E. x ph -> A. x ( ph -> x = z ) )

  proof
    wph
    vx
    wex
    wn
    wph
    wn
    #
    vx
    wal
    wph
    vx
    vz
    weq
    #
    wi
    #
    vx
    wal
    wph
    vx
    alnex
    @0
    @2
    vx
    wph
    @1
    pm2.21
    alimi
    sylbir
end
