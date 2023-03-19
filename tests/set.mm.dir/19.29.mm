include "wal.mm"
include "wex.mm"
include "wa.mm"
include "pm3.2.mm"
include "aleximi.mm"
include "imp.mm"

theorem 19.29
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( A. x ph /\ E. x ps ) -> E. x ( ph /\ ps ) )

  proof
    wph
    vx
    wal
    wps
    vx
    wex
    wph
    wps
    wa
    #
    vx
    wex
    wph
    wps
    @0
    vx
    wph
    wps
    pm3.2
    aleximi
    imp
end
