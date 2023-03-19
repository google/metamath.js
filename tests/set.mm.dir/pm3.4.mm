include "wa.mm"
include "simpr.mm"
include "a1d.mm"

theorem pm3.4
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph /\ ps ) -> ( ph -> ps ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wph
    wps
    simpr
    a1d
end
