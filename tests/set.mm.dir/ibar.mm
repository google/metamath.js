include "wa.mm"
include "pm3.2.mm"
include "simpr.mm"
include "impbid1.mm"

theorem ibar
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps <-> ( ph /\ ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wa
    wph
    wps
    pm3.2
    wph
    wps
    simpr
    impbid1
end
