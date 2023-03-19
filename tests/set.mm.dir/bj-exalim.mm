include "wi.mm"
include "wal.mm"
include "wex.mm"
include "pm2.04.mm"
include "alimi.mm"
include "bj-alexim.mm"
include "3syl.mm"

theorem bj-exalim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( E. x ph -> ( A. x ps -> E. x ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wi
    #
    vx
    wal
    wps
    wph
    wch
    wi
    wi
    #
    vx
    wal
    wps
    vx
    wal
    #
    wph
    vx
    wex
    #
    wch
    vx
    wex
    #
    wi
    wi
    @3
    @2
    @4
    wi
    wi
    @0
    @1
    vx
    wph
    wps
    wch
    pm2.04
    alimi
    wps
    wph
    wch
    vx
    bj-alexim
    @2
    @3
    @4
    pm2.04
    3syl
end
