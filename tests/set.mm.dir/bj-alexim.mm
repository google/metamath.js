include "wi.mm"
include "wal.mm"
include "wex.mm"
include "alim.mm"
include "exim.mm"
include "syl6.mm"

theorem bj-alexim
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( A. x ( ph -> ( ps -> ch ) ) -> ( A. x ph -> ( E. x ps -> E. x ch ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    vx
    wal
    wph
    vx
    wal
    @0
    vx
    wal
    wps
    vx
    wex
    wch
    vx
    wex
    wi
    wph
    @0
    vx
    alim
    wps
    wch
    vx
    exim
    syl6
end
