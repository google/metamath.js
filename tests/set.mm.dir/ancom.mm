include "wa.mm"
include "pm3.22.mm"
include "impbii.mm"

theorem ancom
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) <-> ( ps /\ ph ) )

  proof
    wph
    wps
    wa
    wps
    wph
    wa
    wph
    wps
    pm3.22
    wps
    wph
    pm3.22
    impbii
end
