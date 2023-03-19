include "wi.mm"
include "wex.mm"
include "wal.mm"
include "pm2.27.mm"
include "aleximi.mm"
include "com12.mm"
include "wn.mm"
include "exnal.mm"
include "pm2.21.mm"
include "eximi.mm"
include "sylbir.mm"
include "exa1.mm"
include "ja.mm"
include "impbii.mm"

theorem 19.35
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph -> ps ) <-> ( A. x ph -> E. x ps ) )

  proof
    wph
    wps
    wi
    #
    vx
    wex
    #
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    wi
    @2
    @1
    @3
    wph
    @0
    wps
    vx
    wph
    wps
    pm2.27
    aleximi
    com12
    @2
    @3
    @1
    @2
    wn
    wph
    wn
    #
    vx
    wex
    @1
    wph
    vx
    exnal
    @4
    @0
    vx
    wph
    wps
    pm2.21
    eximi
    sylbir
    wps
    wph
    vx
    exa1
    ja
    impbii
end
