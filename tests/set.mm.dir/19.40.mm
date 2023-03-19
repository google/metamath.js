include "wa.mm"
include "wex.mm"
include "exsimpl.mm"
include "exsimpr.mm"
include "jca.mm"

theorem 19.40
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ( ph /\ ps ) -> ( E. x ph /\ E. x ps ) )

  proof
    wph
    wps
    wa
    vx
    wex
    wph
    vx
    wex
    wps
    vx
    wex
    wph
    wps
    vx
    exsimpl
    wph
    wps
    vx
    exsimpr
    jca
end
