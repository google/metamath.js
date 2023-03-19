include "wa.mm"
include "simpr.mm"
include "a1d.mm"

theorem pm3.4
  let wph: wff ph
  let wps: wff ps


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
