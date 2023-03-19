include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "pm3.45.mm"
include "aleximi.mm"
include "imp.mm"

theorem pm10.56
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x


  assert |- ( ( A. x ( ph -> ps ) /\ E. x ( ph /\ ch ) ) -> E. x ( ps /\ ch ) )

  proof
    wph
    wps
    wi
    #
    vx
    wal
    wph
    wch
    wa
    #
    vx
    wex
    wps
    wch
    wa
    #
    vx
    wex
    @0
    @1
    @2
    vx
    wph
    wps
    wch
    pm3.45
    aleximi
    imp
end
