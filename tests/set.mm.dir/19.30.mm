include "wo.mm"
include "wal.mm"
include "wex.mm"
include "wn.mm"
include "exnal.mm"
include "pm2.53.mm"
include "aleximi.mm"
include "syl5bir.mm"
include "orrd.mm"

theorem 19.30
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ( ph \/ ps ) -> ( A. x ph \/ E. x ps ) )

  proof
    wph
    wps
    wo
    #
    vx
    wal
    #
    wph
    vx
    wal
    #
    wps
    vx
    wex
    #
    @2
    wn
    wph
    wn
    #
    vx
    wex
    @1
    @3
    wph
    vx
    exnal
    @0
    @4
    wps
    vx
    wph
    wps
    pm2.53
    aleximi
    syl5bir
    orrd
end
