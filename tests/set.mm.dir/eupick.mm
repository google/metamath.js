include "weu.mm"
include "wmo.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "eumo.mm"
include "mopick.mm"
include "sylan.mm"

theorem eupick
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( ( E! x ph /\ E. x ( ph /\ ps ) ) -> ( ph -> ps ) )

  proof
    wph
    vx
    weu
    wph
    vx
    wmo
    wph
    wps
    wa
    vx
    wex
    wph
    wps
    wi
    wph
    vx
    eumo
    wph
    wps
    vx
    mopick
    sylan
end
