include "wal.mm"
include "wex.mm"
include "wa.mm"
include "pm3.21.mm"
include "aleximi.mm"
include "impcom.mm"

theorem 19.29r
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E. x ph /\ A. x ps ) -> E. x ( ph /\ ps ) )

  proof
    wps
    vx
    wal
    wph
    vx
    wex
    wph
    wps
    wa
    #
    vx
    wex
    wps
    wph
    @0
    vx
    wps
    wph
    pm3.21
    aleximi
    impcom
end
