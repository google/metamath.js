include "wal.mm"
include "wex.mm"
include "wi.mm"
include "ala1.mm"
include "exim.mm"
include "syl.mm"
include "com12.mm"

theorem bj-axdd2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ph -> ( A. x ps -> E. x ps ) )

  proof
    wps
    vx
    wal
    #
    wph
    vx
    wex
    #
    wps
    vx
    wex
    #
    @0
    wph
    wps
    wi
    vx
    wal
    @1
    @2
    wi
    wps
    wph
    vx
    ala1
    wph
    wps
    vx
    exim
    syl
    com12
end
